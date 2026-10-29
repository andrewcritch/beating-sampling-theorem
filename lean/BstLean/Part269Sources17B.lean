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
import BstLean.Part269Direction17
import BstLean.Part269Shared17
import BstLean.Part269Finite
import BstLean.Part269Rows17
import BstLean.Part269Source
/-! Actual 12788 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12788
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12788 ≤ (1.035684716781 : ℝ) := by
  have hr : (113.084039545817 : ℝ) ≤ √(12788 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.084039545817 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12788 12788 (11 / 1000) ≤
    (0.008452890502 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12788) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.084039545817 : ℝ) ≤ √(12788 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12788)
  have hdiv : K / √(12788 : ℝ) ≤ K / 113.084039545817 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.084039545817 ≤ (0.008452890502 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12788.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12788 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12788 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12788 := gPlus_lower 12788
end BstLean.Part269.N12788

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12788
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035684716780 : ℝ) ≤ wn 12788 := by
  have hn : √(12788 : ℝ) ≤ 113.084039545818 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12788 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.084039545818 ≤ 2 / √(12788 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000250117495 : ℝ) ≤ rhoBar 12788 BstLean.Part154.csC ∧
    rhoBar 12788 BstLean.Part154.csC ≤ 0.000250117883 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035684716780 : ℝ) / (1.295212 * 12788) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035684716781 : ℝ) / (1.29521 * 12788) := by gcongr
      _ ≤ (0.000250117883 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12788 BstLean.Part154.csC) ≤ 0.001000534091 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12788 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12788 BstLean.Part154.csC) (piBar (rhoBar 12788 BstLean.Part154.csC)) ≤ 0.000191041664 ∧
    cc1 (rhoBar 12788 BstLean.Part154.csC) (piBar (rhoBar 12788 BstLean.Part154.csC)) ≤ 0.000121561092 ∧
    cc2 (rhoBar 12788 BstLean.Part154.csC) ≤ 0.000070567161 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12788 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12788 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12788 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12788 BstLean.Part154.csC * nuR (rhoBar 12788 BstLean.Part154.csC)) ≤ 0.000500251406 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000250117883 : ℝ) * 0.001000534091 := by gcongr
      _ ≤ (0.000500251406 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12788 BstLean.Part154.csC) * nuR (rhoBar 12788 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001000534091 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12788 BstLean.Part154.csC) * rhoBar 12788 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000250117883 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000250117883 / 2 + 0.399 * 0.001000534091 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000191041664 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000500251406 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121561092 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000250117883 / 1.414213562 := by gcongr
      _ ≤ (0.000070567161 : ℝ) := by norm_num

end BstLean.Part269.N12788

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12788
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12788 BstLean.Part154.csC) (piBar (rhoBar 12788 BstLean.Part154.csC)) ≤ 1.57613E-7 := by
  have hr0 : 0 ≤ rhoBar 12788 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12788 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12788 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12788 BstLean.Part154.csC) (piBar (rhoBar 12788 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12788 BstLean.Part154.csC) (piBar (rhoBar 12788 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12788 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000191041664 : ℝ) ^ 2 + 0.000121561092 ^ 2 + 3 * 0.000070567161 ^ 2 +
        2 * 0.797885 * 0.000191041664 * 0.000121561092 + 2 * 0.000191041664 * 0.000070567161 +
        4 * 0.797885 * 0.000121561092 * 0.000070567161 := by gcongr
    _ ≤ (1.57613E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12788 BstLean.Part154.csC Θ ≤ 0.002610571089 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12788 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12788 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12788 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12788 BstLean.Part154.csC) (piBar (rhoBar 12788 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12788 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035684716781 * 1.57613E-7 / (0.000250117495 : ℝ) := by gcongr
    _ ≤ 0.002610571089 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12788 BstLean.Part154.csC Θ ≤ 0.002896216598 + 0.000659648405 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12788 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12788 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12788 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035684716781 : ℝ) * ((2 * Θ * 0.000250117883 +
        (6863 / 10000) * 0.000250117883 * 12788 * 0.001000534091) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002896216598 + 0.000659648405 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12788 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12788 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12788 0.011 Θ ∧ gammaRatio 12788 0.011 Θ ≤ 0.000085984060 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12788 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035684716781 : ℝ) * 0.525 / ((1 - 0.011) * 12788) := by gcongr
      _ ≤ (0.000085984060 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12788 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12788 0.011 Θ) :=
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
    badAllowance 12788 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000560204559 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12788 BstLean.Part154.csC) 1.22 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 2 (rhoBar 12788 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12788 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12788 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12788 0.011 Θ) 1.12 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 1 (gammaRatio 12788 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12788 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12788 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12788 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12788 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035684716781 : ℝ) * 12788 *
        (1.8602E-8 / 1.1045361 + 2.2721E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000560204559 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12788 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003456421157 + 0.003270219494 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12788

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12788
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12788 BstLean.Part154.csC) (piBar (rhoBar 12788 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12788 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12788 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12788 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12788 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12788 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12788 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12788 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12788 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12788 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12788 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12788 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12788 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12788 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12788 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052301462154 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12788) ≤ 0.010560620101 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12788 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035684716781)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010560620101 + 2 * 0.737676 / 12788) := by gcongr
    _ ≤ (0.052301462154 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12788 12 ≤ 0.0015 := by
  exact BstLean.Part269.S17.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12788

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12788
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560507520527 : ℝ) ≤ plow 12788 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12788) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052679886392)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001370549822) : eMP 12788 0.011 xi bn ≤ 0.001180037446 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12788 : ℝ) * (1 - 0.011))) ≤ 0.000583475890 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001370549822 / (12788 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000583475890 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000583475890 : ℝ) + 3.141593 * 0.052679886392 / (12788 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001180037446 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052679886392)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001370549822) : PiBarMP 12788 12 0.011 xi bn ≤ 0.160689801526 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12788 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037020937617 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.460357459862 : ℝ) ≤ √((12788 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.084039545817 : ℝ) ≤ √(12788 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12788) ≤ 0.123204019937 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037020937617 + 0.052679886392 * 1.772454 / (2 * (112.460357459862 : ℝ))) * (1 + 0.001180037446) +
        8 / (12788 * 113.084039545817) + 0.123204019937 := by gcongr
    _ ≤ (0.160689801526 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052679886392)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001370549822) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281822455512) :
    parallelOracle 12788 0.011 xi bn cd ≤ 0.161673559229 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12788 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12788 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560507520527 : ℝ) ≤ plow 12788 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.084039545817 : ℝ) ≤ √(12788 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281822455512 : ℝ) / (2 * 0.560507520527 * 113.084039545817)) * 0.160689801526 +
        0.281822455512 ^ 2 / (2 * 0.560507520527 * 113.084039545817) := by gcongr
    _ ≤ (0.161673559229 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052679886392) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001370549822)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281822455512) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12788 12788 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560507520527 : ℝ) ≤ plow 12788 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.084039545817 : ℝ) ≤ √(12788 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12788 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12788 Θ 1.22 ≤ 0.011726681372 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.084039545817 := by gcongr <;> linarith
      _ ≤ (0.011726681372 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12788 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12788 12788 0.011 ≤ 0.008452890502 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12788 12788 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12788 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12788 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12788 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12788 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161673559229 + 0.011726681372 + (0.008452890502 : ℝ) *
        (1 + 2 * (0.281822455512 + 0.011726681372) / (0.560507520527 * 113.084039545817))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12788]

end BstLean.Part269.N12788

/-! The original eight local profiles supply actual 12788 moment certificates. -/
namespace BstLean.Part269.N12788
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12788 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12788 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12788 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052679886392 ∧
    0 ≤ bN 12788 BstLean.Part154.csC (groupTheta g) ∧ bN 12788 BstLean.Part154.csC (groupTheta g) ≤ 0.001370549822 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12788 12788 0.011
      (momentAllowance 12788 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12788 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12788 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12788 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12788 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12788 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229520993358 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12788 0.011
      (momentAllowance 12788 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12788 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12788
/-! The actual computed-centre upper energy formula at 12788. -/
namespace BstLean.Part269.N12788
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12788

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12788
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12788)
open BstLean.Part268 (cell12788)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085237698075
  | 2 => 0.086175898326
  | 3 => 0.087111589389
  | 4 => 0.088046038832
  | 5 => 0.088980784645
  | 6 => 0.089917676017
  | 7 => 0.090858918070
  | 8 => 0.091807120601
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12788 12788 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12788 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003459522332 + 0.003273654356 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S17.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12788

/-! Actual upper energy certificates on all 43 source endpoints at 12788. -/
namespace BstLean.Part269.N12788
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12788)
open BstLean.Part268 (cell12788)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12788 (gMinus 12788) (1 - (cell12788 i).lower) ≤ 1 ∧
    energyUpper 12788 (gMinus 12788) (BstLean.Part211.gPlus 12788)
      (finiteEnergy 12788 12788 0.011) (1 - (cell12788 i).lower) ≤
      (cell12788 i).energy := by
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
      have E := BstLean.Part269.S17.uniformEnergy10 (n := 12788) (by norm_num)
        (q := 1 - (cell12788 ⟨10,by decide⟩).lower)
        (by norm_num [cell12788]) (by norm_num [cell12788])
      exact ⟨E.1,E.2.trans (by norm_num [cell12788])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy11 (n := 12788) (by norm_num)
        (q := 1 - (cell12788 ⟨11,by decide⟩).lower)
        (by norm_num [cell12788]) (by norm_num [cell12788])
      exact ⟨E.1,E.2.trans (by norm_num [cell12788])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy12 (n := 12788) (by norm_num)
        (q := 1 - (cell12788 ⟨12,by decide⟩).lower)
        (by norm_num [cell12788]) (by norm_num [cell12788])
      exact ⟨E.1,E.2.trans (by norm_num [cell12788])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy13 (n := 12788) (by norm_num)
        (q := 1 - (cell12788 ⟨13,by decide⟩).lower)
        (by norm_num [cell12788]) (by norm_num [cell12788])
      exact ⟨E.1,E.2.trans (by norm_num [cell12788])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy14 (n := 12788) (by norm_num)
        (q := 1 - (cell12788 ⟨14,by decide⟩).lower)
        (by norm_num [cell12788]) (by norm_num [cell12788])
      exact ⟨E.1,E.2.trans (by norm_num [cell12788])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy15 (n := 12788) (by norm_num)
        (q := 1 - (cell12788 ⟨15,by decide⟩).lower)
        (by norm_num [cell12788]) (by norm_num [cell12788])
      exact ⟨E.1,E.2.trans (by norm_num [cell12788])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy16 (n := 12788) (by norm_num)
        (q := 1 - (cell12788 ⟨16,by decide⟩).lower)
        (by norm_num [cell12788]) (by norm_num [cell12788])
      exact ⟨E.1,E.2.trans (by norm_num [cell12788])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy17 (n := 12788) (by norm_num)
        (q := 1 - (cell12788 ⟨17,by decide⟩).lower)
        (by norm_num [cell12788]) (by norm_num [cell12788])
      exact ⟨E.1,E.2.trans (by norm_num [cell12788])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy18 (n := 12788) (by norm_num)
        (q := 1 - (cell12788 ⟨18,by decide⟩).lower)
        (by norm_num [cell12788]) (by norm_num [cell12788])
      exact ⟨E.1,E.2.trans (by norm_num [cell12788])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy19 (n := 12788) (by norm_num)
        (q := 1 - (cell12788 ⟨19,by decide⟩).lower)
        (by norm_num [cell12788]) (by norm_num [cell12788])
      exact ⟨E.1,E.2.trans (by norm_num [cell12788])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy20 (n := 12788) (by norm_num)
        (q := 1 - (cell12788 ⟨20,by decide⟩).lower)
        (by norm_num [cell12788]) (by norm_num [cell12788])
      exact ⟨E.1,E.2.trans (by norm_num [cell12788])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy21 (n := 12788) (by norm_num)
        (q := 1 - (cell12788 ⟨21,by decide⟩).lower)
        (by norm_num [cell12788]) (by norm_num [cell12788])
      exact ⟨E.1,E.2.trans (by norm_num [cell12788])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy22 (n := 12788) (by norm_num)
        (q := 1 - (cell12788 ⟨22,by decide⟩).lower)
        (by norm_num [cell12788]) (by norm_num [cell12788])
      exact ⟨E.1,E.2.trans (by norm_num [cell12788])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy23 (n := 12788) (by norm_num)
        (q := 1 - (cell12788 ⟨23,by decide⟩).lower)
        (by norm_num [cell12788]) (by norm_num [cell12788])
      exact ⟨E.1,E.2.trans (by norm_num [cell12788])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy24 (n := 12788) (by norm_num)
        (q := 1 - (cell12788 ⟨24,by decide⟩).lower)
        (by norm_num [cell12788]) (by norm_num [cell12788])
      exact ⟨E.1,E.2.trans (by norm_num [cell12788])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy25 (n := 12788) (by norm_num)
        (q := 1 - (cell12788 ⟨25,by decide⟩).lower)
        (by norm_num [cell12788]) (by norm_num [cell12788])
      exact ⟨E.1,E.2.trans (by norm_num [cell12788])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy26 (n := 12788) (by norm_num)
        (q := 1 - (cell12788 ⟨26,by decide⟩).lower)
        (by norm_num [cell12788]) (by norm_num [cell12788])
      exact ⟨E.1,E.2.trans (by norm_num [cell12788])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy27 (n := 12788) (by norm_num)
        (q := 1 - (cell12788 ⟨27,by decide⟩).lower)
        (by norm_num [cell12788]) (by norm_num [cell12788])
      exact ⟨E.1,E.2.trans (by norm_num [cell12788])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy28 (n := 12788) (by norm_num)
        (q := 1 - (cell12788 ⟨28,by decide⟩).lower)
        (by norm_num [cell12788]) (by norm_num [cell12788])
      exact ⟨E.1,E.2.trans (by norm_num [cell12788])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy29 (n := 12788) (by norm_num)
        (q := 1 - (cell12788 ⟨29,by decide⟩).lower)
        (by norm_num [cell12788]) (by norm_num [cell12788])
      exact ⟨E.1,E.2.trans (by norm_num [cell12788])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy30 (n := 12788) (by norm_num)
        (q := 1 - (cell12788 ⟨30,by decide⟩).lower)
        (by norm_num [cell12788]) (by norm_num [cell12788])
      exact ⟨E.1,E.2.trans (by norm_num [cell12788])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy31 (n := 12788) (by norm_num)
        (q := 1 - (cell12788 ⟨31,by decide⟩).lower)
        (by norm_num [cell12788]) (by norm_num [cell12788])
      exact ⟨E.1,E.2.trans (by norm_num [cell12788])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy32 (n := 12788) (by norm_num)
        (q := 1 - (cell12788 ⟨32,by decide⟩).lower)
        (by norm_num [cell12788]) (by norm_num [cell12788])
      exact ⟨E.1,E.2.trans (by norm_num [cell12788])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy33 (n := 12788) (by norm_num)
        (q := 1 - (cell12788 ⟨33,by decide⟩).lower)
        (by norm_num [cell12788]) (by norm_num [cell12788])
      exact ⟨E.1,E.2.trans (by norm_num [cell12788])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy34 (n := 12788) (by norm_num)
        (q := 1 - (cell12788 ⟨34,by decide⟩).lower)
        (by norm_num [cell12788]) (by norm_num [cell12788])
      exact ⟨E.1,E.2.trans (by norm_num [cell12788])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy35 (n := 12788) (by norm_num)
        (q := 1 - (cell12788 ⟨35,by decide⟩).lower)
        (by norm_num [cell12788]) (by norm_num [cell12788])
      exact ⟨E.1,E.2.trans (by norm_num [cell12788])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy36 (n := 12788) (by norm_num)
        (q := 1 - (cell12788 ⟨36,by decide⟩).lower)
        (by norm_num [cell12788]) (by norm_num [cell12788])
      exact ⟨E.1,E.2.trans (by norm_num [cell12788])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy37 (n := 12788) (by norm_num)
        (q := 1 - (cell12788 ⟨37,by decide⟩).lower)
        (by norm_num [cell12788]) (by norm_num [cell12788])
      exact ⟨E.1,E.2.trans (by norm_num [cell12788])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy38 (n := 12788) (by norm_num)
        (q := 1 - (cell12788 ⟨38,by decide⟩).lower)
        (by norm_num [cell12788]) (by norm_num [cell12788])
      exact ⟨E.1,E.2.trans (by norm_num [cell12788])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy39 (n := 12788) (by norm_num)
        (q := 1 - (cell12788 ⟨39,by decide⟩).lower)
        (by norm_num [cell12788]) (by norm_num [cell12788])
      exact ⟨E.1,E.2.trans (by norm_num [cell12788])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy40 (n := 12788) (by norm_num)
        (q := 1 - (cell12788 ⟨40,by decide⟩).lower)
        (by norm_num [cell12788]) (by norm_num [cell12788])
      exact ⟨E.1,E.2.trans (by norm_num [cell12788])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy41 (n := 12788) (by norm_num)
        (q := 1 - (cell12788 ⟨41,by decide⟩).lower)
        (by norm_num [cell12788]) (by norm_num [cell12788])
      exact ⟨E.1,E.2.trans (by norm_num [cell12788])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy42 (n := 12788) (by norm_num)
        (q := 1 - (cell12788 ⟨42,by decide⟩).lower)
        (by norm_num [cell12788]) (by norm_num [cell12788])
      exact ⟨E.1,E.2.trans (by norm_num [cell12788])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy43 (n := 12788) (by norm_num)
        (q := 1 - (cell12788 ⟨43,by decide⟩).lower)
        (by norm_num [cell12788]) (by norm_num [cell12788])
      exact ⟨E.1,E.2.trans (by norm_num [cell12788])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy44 (n := 12788) (by norm_num)
        (q := 1 - (cell12788 ⟨44,by decide⟩).lower)
        (by norm_num [cell12788]) (by norm_num [cell12788])
      exact ⟨E.1,E.2.trans (by norm_num [cell12788])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy45 (n := 12788) (by norm_num)
        (q := 1 - (cell12788 ⟨45,by decide⟩).lower)
        (by norm_num [cell12788]) (by norm_num [cell12788])
      exact ⟨E.1,E.2.trans (by norm_num [cell12788])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy46 (n := 12788) (by norm_num)
        (q := 1 - (cell12788 ⟨46,by decide⟩).lower)
        (by norm_num [cell12788]) (by norm_num [cell12788])
      exact ⟨E.1,E.2.trans (by norm_num [cell12788])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy47 (n := 12788) (by norm_num)
        (q := 1 - (cell12788 ⟨47,by decide⟩).lower)
        (by norm_num [cell12788]) (by norm_num [cell12788])
      exact ⟨E.1,E.2.trans (by norm_num [cell12788])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy48 (n := 12788) (by norm_num)
        (q := 1 - (cell12788 ⟨48,by decide⟩).lower)
        (by norm_num [cell12788]) (by norm_num [cell12788])
      exact ⟨E.1,E.2.trans (by norm_num [cell12788])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy49 (n := 12788) (by norm_num)
        (q := 1 - (cell12788 ⟨49,by decide⟩).lower)
        (by norm_num [cell12788]) (by norm_num [cell12788])
      exact ⟨E.1,E.2.trans (by norm_num [cell12788])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy50 (n := 12788) (by norm_num)
        (q := 1 - (cell12788 ⟨50,by decide⟩).lower)
        (by norm_num [cell12788]) (by norm_num [cell12788])
      exact ⟨E.1,E.2.trans (by norm_num [cell12788])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy51 (n := 12788) (by norm_num)
        (q := 1 - (cell12788 ⟨51,by decide⟩).lower)
        (by norm_num [cell12788]) (by norm_num [cell12788])
      exact ⟨E.1,E.2.trans (by norm_num [cell12788])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy52 (n := 12788) (by norm_num)
        (q := 1 - (cell12788 ⟨52,by decide⟩).lower)
        (by norm_num [cell12788]) (by norm_num [cell12788])
      exact ⟨E.1,E.2.trans (by norm_num [cell12788])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12788

/-! Source-cell containment and simple scalar guards at 12788. -/
namespace BstLean.Part269.N12788
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12788)
open BstLean.Part268 (cell12788)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12788 ⟨10,by decide⟩).lower ∧ (cell12788 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12788 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12788 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12788 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12788 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12788 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12788,cell12788,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12788 ⟨11,by decide⟩).lower ∧ (cell12788 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12788 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12788 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12788 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12788 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12788 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12788,cell12788,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12788 ⟨12,by decide⟩).lower ∧ (cell12788 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12788 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12788 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12788 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12788 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12788 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12788,cell12788,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12788 ⟨13,by decide⟩).lower ∧ (cell12788 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12788 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12788 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12788 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12788 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12788 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12788,cell12788,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12788 ⟨14,by decide⟩).lower ∧ (cell12788 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12788 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12788 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12788 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12788 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12788 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12788,cell12788,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12788 ⟨15,by decide⟩).lower ∧ (cell12788 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12788 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12788 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12788 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12788 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12788 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12788,cell12788,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12788 ⟨16,by decide⟩).lower ∧ (cell12788 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12788 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12788 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12788 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12788 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12788 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12788,cell12788,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12788 ⟨17,by decide⟩).lower ∧ (cell12788 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12788 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12788 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12788 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12788 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12788 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12788,cell12788,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12788 ⟨18,by decide⟩).lower ∧ (cell12788 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12788 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12788 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12788 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12788 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12788 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12788,cell12788,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12788 ⟨19,by decide⟩).lower ∧ (cell12788 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12788 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12788 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12788 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12788 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12788 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12788,cell12788,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12788 ⟨20,by decide⟩).lower ∧ (cell12788 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12788 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12788 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12788 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12788 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12788 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12788,cell12788,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12788 ⟨21,by decide⟩).lower ∧ (cell12788 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12788 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12788 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12788 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12788 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12788 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12788,cell12788,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12788 ⟨22,by decide⟩).lower ∧ (cell12788 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12788 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12788 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12788 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12788 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12788 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12788,cell12788,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12788 ⟨23,by decide⟩).lower ∧ (cell12788 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12788 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12788 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12788 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12788 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12788 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12788,cell12788,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12788 ⟨24,by decide⟩).lower ∧ (cell12788 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12788 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12788 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12788 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12788 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12788 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12788,cell12788,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12788 ⟨25,by decide⟩).lower ∧ (cell12788 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12788 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12788 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12788 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12788 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12788 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12788,cell12788,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12788 ⟨26,by decide⟩).lower ∧ (cell12788 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12788 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12788 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12788 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12788 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12788 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12788,cell12788,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12788 ⟨27,by decide⟩).lower ∧ (cell12788 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12788 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12788 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12788 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12788 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12788 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12788,cell12788,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12788 ⟨28,by decide⟩).lower ∧ (cell12788 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12788 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12788 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12788 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12788 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12788 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12788,cell12788,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12788 ⟨29,by decide⟩).lower ∧ (cell12788 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12788 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12788 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12788 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12788 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12788 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12788,cell12788,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12788 ⟨30,by decide⟩).lower ∧ (cell12788 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12788 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12788 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12788 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12788 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12788 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12788,cell12788,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12788 ⟨31,by decide⟩).lower ∧ (cell12788 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12788 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12788 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12788 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12788 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12788 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12788,cell12788,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12788 ⟨32,by decide⟩).lower ∧ (cell12788 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12788 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12788 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12788 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12788 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12788 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12788,cell12788,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12788 ⟨33,by decide⟩).lower ∧ (cell12788 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12788 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12788 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12788 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12788 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12788 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12788,cell12788,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12788 ⟨34,by decide⟩).lower ∧ (cell12788 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12788 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12788 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12788 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12788 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12788 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12788,cell12788,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12788 ⟨35,by decide⟩).lower ∧ (cell12788 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12788 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12788 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12788 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12788 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12788 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12788,cell12788,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12788 ⟨36,by decide⟩).lower ∧ (cell12788 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12788 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12788 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12788 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12788 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12788 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12788,cell12788,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12788 ⟨37,by decide⟩).lower ∧ (cell12788 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12788 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12788 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12788 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12788 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12788 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12788,cell12788,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12788 ⟨38,by decide⟩).lower ∧ (cell12788 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12788 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12788 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12788 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12788 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12788 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12788,cell12788,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12788 ⟨39,by decide⟩).lower ∧ (cell12788 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12788 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12788 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12788 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12788 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12788 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12788,cell12788,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12788 ⟨40,by decide⟩).lower ∧ (cell12788 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12788 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12788 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12788 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12788 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12788 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12788,cell12788,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12788 ⟨41,by decide⟩).lower ∧ (cell12788 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12788 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12788 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12788 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12788 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12788 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12788,cell12788,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12788 ⟨42,by decide⟩).lower ∧ (cell12788 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12788 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12788 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12788 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12788 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12788 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12788,cell12788,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12788 ⟨43,by decide⟩).lower ∧ (cell12788 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12788 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12788 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12788 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12788 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12788 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12788,cell12788,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12788 ⟨44,by decide⟩).lower ∧ (cell12788 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12788 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12788 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12788 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12788 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12788 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12788,cell12788,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12788 ⟨45,by decide⟩).lower ∧ (cell12788 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12788 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12788 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12788 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12788 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12788 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12788,cell12788,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12788 ⟨46,by decide⟩).lower ∧ (cell12788 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12788 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12788 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12788 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12788 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12788 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12788,cell12788,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12788 ⟨47,by decide⟩).lower ∧ (cell12788 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12788 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12788 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12788 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12788 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12788 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12788,cell12788,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12788 ⟨48,by decide⟩).lower ∧ (cell12788 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12788 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12788 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12788 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12788 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12788 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12788,cell12788,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12788 ⟨49,by decide⟩).lower ∧ (cell12788 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12788 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12788 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12788 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12788 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12788 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12788,cell12788,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12788 ⟨50,by decide⟩).lower ∧ (cell12788 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12788 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12788 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12788 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12788 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12788 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12788,cell12788,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12788 ⟨51,by decide⟩).lower ∧ (cell12788 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12788 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12788 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12788 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12788 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12788 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12788,cell12788,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12788 ⟨52,by decide⟩).lower ∧ (cell12788 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12788 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12788 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12788 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12788 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12788 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12788,cell12788,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12788 i).lower ∧
    (cell12788 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12788 i).upper ≤ (0.532 : ℝ) ∧
    (cell12788 i).centre ≤ (0.1 : ℝ) ∧ (cell12788 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12788 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12788 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12788

/-! The local source numeric instances at 12788 have no network premises. -/
namespace BstLean.Part269.N12788
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12788)
open BstLean.Part268 (cell12788)

noncomputable def sourceNumerics12788 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12788 (cell12788 i)
      scalarRow12788.M scalarRow12788.H scalarRow12788.xi := by
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
    energy_allowance := scalarRow12788.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12788]
    centre_nonneg := (scalarRow12788.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D17.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12788])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12788
/-! Actual 12789 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12789
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12789 ≤ (1.035683309391 : ℝ) := by
  have hr : (113.088460949824 : ℝ) ≤ √(12789 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.088460949824 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12789 12789 (11 / 1000) ≤
    (0.008452560018 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12789) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.088460949824 : ℝ) ≤ √(12789 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12789)
  have hdiv : K / √(12789 : ℝ) ≤ K / 113.088460949824 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.088460949824 ≤ (0.008452560018 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12789.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12789 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12789 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12789 := gPlus_lower 12789
end BstLean.Part269.N12789

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12789
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035683309390 : ℝ) ≤ wn 12789 := by
  have hn : √(12789 : ℝ) ≤ 113.088460949825 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12789 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.088460949825 ≤ 2 / √(12789 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000250097598 : ℝ) ≤ rhoBar 12789 BstLean.Part154.csC ∧
    rhoBar 12789 BstLean.Part154.csC ≤ 0.000250097985 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035683309390 : ℝ) / (1.295212 * 12789) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035683309391 : ℝ) / (1.29521 * 12789) := by gcongr
      _ ≤ (0.000250097985 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12789 BstLean.Part154.csC) ≤ 0.001000454490 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12789 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12789 BstLean.Part154.csC) (piBar (rhoBar 12789 BstLean.Part154.csC)) ≤ 0.000191026465 ∧
    cc1 (rhoBar 12789 BstLean.Part154.csC) (piBar (rhoBar 12789 BstLean.Part154.csC)) ≤ 0.000121551421 ∧
    cc2 (rhoBar 12789 BstLean.Part154.csC) ≤ 0.000070561547 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12789 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12789 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12789 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12789 BstLean.Part154.csC * nuR (rhoBar 12789 BstLean.Part154.csC)) ≤ 0.000500211608 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000250097985 : ℝ) * 0.001000454490 := by gcongr
      _ ≤ (0.000500211608 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12789 BstLean.Part154.csC) * nuR (rhoBar 12789 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001000454490 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12789 BstLean.Part154.csC) * rhoBar 12789 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000250097985 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000250097985 / 2 + 0.399 * 0.001000454490 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000191026465 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000500211608 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121551421 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000250097985 / 1.414213562 := by gcongr
      _ ≤ (0.000070561547 : ℝ) := by norm_num

end BstLean.Part269.N12789

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12789
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12789 BstLean.Part154.csC) (piBar (rhoBar 12789 BstLean.Part154.csC)) ≤ 1.57588E-7 := by
  have hr0 : 0 ≤ rhoBar 12789 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12789 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12789 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12789 BstLean.Part154.csC) (piBar (rhoBar 12789 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12789 BstLean.Part154.csC) (piBar (rhoBar 12789 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12789 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000191026465 : ℝ) ^ 2 + 0.000121551421 ^ 2 + 3 * 0.000070561547 ^ 2 +
        2 * 0.797885 * 0.000191026465 * 0.000121551421 + 2 * 0.000191026465 * 0.000070561547 +
        4 * 0.797885 * 0.000121551421 * 0.000070561547 := by gcongr
    _ ≤ (1.57588E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12789 BstLean.Part154.csC Θ ≤ 0.002610361118 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12789 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12789 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12789 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12789 BstLean.Part154.csC) (piBar (rhoBar 12789 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12789 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035683309391 * 1.57588E-7 / (0.000250097598 : ℝ) := by gcongr
    _ ≤ 0.002610361118 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12789 BstLean.Part154.csC Θ ≤ 0.002895978299 + 0.000659595031 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12789 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12789 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12789 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035683309391 : ℝ) * ((2 * Θ * 0.000250097985 +
        (6863 / 10000) * 0.000250097985 * 12789 * 0.001000454490) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002895978299 + 0.000659595031 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12789 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12789 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12789 0.011 Θ ∧ gammaRatio 12789 0.011 Θ ≤ 0.000085977220 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12789 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035683309391 : ℝ) * 0.525 / ((1 - 0.011) * 12789) := by gcongr
      _ ≤ (0.000085977220 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12789 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12789 0.011 Θ) :=
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
    badAllowance 12789 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000560204559 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12789 BstLean.Part154.csC) 1.22 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 2 (rhoBar 12789 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12789 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12789 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12789 0.011 Θ) 1.12 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 1 (gammaRatio 12789 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12789 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12789 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12789 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12789 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035683309391 : ℝ) * 12789 *
        (1.8602E-8 / 1.1045361 + 2.2721E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000560204559 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12789 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003456182858 + 0.003269956149 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12789

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12789
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12789 BstLean.Part154.csC) (piBar (rhoBar 12789 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12789 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12789 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12789 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12789 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12789 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12789 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12789 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12789 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12789 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12789 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12789 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12789 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12789 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12789 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052299395235 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12789) ≤ 0.010560207214 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12789 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035683309391)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010560207214 + 2 * 0.737676 / 12789) := by gcongr
    _ ≤ (0.052299395235 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12789 12 ≤ 0.0015 := by
  exact BstLean.Part269.S17.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12789

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12789
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560507565126 : ℝ) ≤ plow 12789 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12789) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052679509837)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001370439587) : eMP 12789 0.011 xi bn ≤ 0.001179943776 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12789 : ℝ) * (1 - 0.011))) ≤ 0.000583429613 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001370439587 / (12789 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000583429613 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000583429613 : ℝ) + 3.141593 * 0.052679509837 / (12789 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001179943776 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052679509837)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001370439587) : PiBarMP 12789 12 0.011 xi bn ≤ 0.160683470653 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12789 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037019448767 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.464754478903 : ℝ) ≤ √((12789 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.088460949824 : ℝ) ≤ √(12789 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12789) ≤ 0.123199203047 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037019448767 + 0.052679509837 * 1.772454 / (2 * (112.464754478903 : ℝ))) * (1 + 0.001179943776) +
        8 / (12789 * 113.088460949824) + 0.123199203047 := by gcongr
    _ ≤ (0.160683470653 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052679509837)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001370439587) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281819568286) :
    parallelOracle 12789 0.011 xi bn cd ≤ 0.161667159246 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12789 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12789 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560507565126 : ℝ) ≤ plow 12789 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.088460949824 : ℝ) ≤ √(12789 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281819568286 : ℝ) / (2 * 0.560507565126 * 113.088460949824)) * 0.160683470653 +
        0.281819568286 ^ 2 / (2 * 0.560507565126 * 113.088460949824) := by gcongr
    _ ≤ (0.161667159246 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052679509837) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001370439587)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281819568286) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12789 12789 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560507565126 : ℝ) ≤ plow 12789 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.088460949824 : ℝ) ≤ √(12789 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12789 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12789 Θ 1.22 ≤ 0.011726222896 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.088460949824 := by gcongr <;> linarith
      _ ≤ (0.011726222896 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12789 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12789 12789 0.011 ≤ 0.008452560018 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12789 12789 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12789 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12789 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12789 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12789 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161667159246 + 0.011726222896 + (0.008452560018 : ℝ) *
        (1 + 2 * (0.281819568286 + 0.011726222896) / (0.560507565126 * 113.088460949824))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12789]

end BstLean.Part269.N12789

/-! The original eight local profiles supply actual 12789 moment certificates. -/
namespace BstLean.Part269.N12789
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12789 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12789 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12789 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052679509837 ∧
    0 ≤ bN 12789 BstLean.Part154.csC (groupTheta g) ∧ bN 12789 BstLean.Part154.csC (groupTheta g) ≤ 0.001370439587 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12789 12789 0.011
      (momentAllowance 12789 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12789 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12789 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12789 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12789 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12789 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229520173051 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12789 0.011
      (momentAllowance 12789 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12789 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12789
/-! The actual computed-centre upper energy formula at 12789. -/
namespace BstLean.Part269.N12789
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12789

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12789
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12789)
open BstLean.Part268 (cell12789)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085234873568
  | 2 => 0.086173023962
  | 3 => 0.087108658224
  | 4 => 0.088043042304
  | 5 => 0.088977712279
  | 6 => 0.089914515100
  | 7 => 0.090855653283
  | 8 => 0.091803733613
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12789 12789 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12789 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003459522332 + 0.003273654356 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S17.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12789

/-! Actual upper energy certificates on all 43 source endpoints at 12789. -/
namespace BstLean.Part269.N12789
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12789)
open BstLean.Part268 (cell12789)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12789 (gMinus 12789) (1 - (cell12789 i).lower) ≤ 1 ∧
    energyUpper 12789 (gMinus 12789) (BstLean.Part211.gPlus 12789)
      (finiteEnergy 12789 12789 0.011) (1 - (cell12789 i).lower) ≤
      (cell12789 i).energy := by
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
      have E := BstLean.Part269.S17.uniformEnergy10 (n := 12789) (by norm_num)
        (q := 1 - (cell12789 ⟨10,by decide⟩).lower)
        (by norm_num [cell12789]) (by norm_num [cell12789])
      exact ⟨E.1,E.2.trans (by norm_num [cell12789])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy11 (n := 12789) (by norm_num)
        (q := 1 - (cell12789 ⟨11,by decide⟩).lower)
        (by norm_num [cell12789]) (by norm_num [cell12789])
      exact ⟨E.1,E.2.trans (by norm_num [cell12789])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy12 (n := 12789) (by norm_num)
        (q := 1 - (cell12789 ⟨12,by decide⟩).lower)
        (by norm_num [cell12789]) (by norm_num [cell12789])
      exact ⟨E.1,E.2.trans (by norm_num [cell12789])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy13 (n := 12789) (by norm_num)
        (q := 1 - (cell12789 ⟨13,by decide⟩).lower)
        (by norm_num [cell12789]) (by norm_num [cell12789])
      exact ⟨E.1,E.2.trans (by norm_num [cell12789])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy14 (n := 12789) (by norm_num)
        (q := 1 - (cell12789 ⟨14,by decide⟩).lower)
        (by norm_num [cell12789]) (by norm_num [cell12789])
      exact ⟨E.1,E.2.trans (by norm_num [cell12789])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy15 (n := 12789) (by norm_num)
        (q := 1 - (cell12789 ⟨15,by decide⟩).lower)
        (by norm_num [cell12789]) (by norm_num [cell12789])
      exact ⟨E.1,E.2.trans (by norm_num [cell12789])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy16 (n := 12789) (by norm_num)
        (q := 1 - (cell12789 ⟨16,by decide⟩).lower)
        (by norm_num [cell12789]) (by norm_num [cell12789])
      exact ⟨E.1,E.2.trans (by norm_num [cell12789])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy17 (n := 12789) (by norm_num)
        (q := 1 - (cell12789 ⟨17,by decide⟩).lower)
        (by norm_num [cell12789]) (by norm_num [cell12789])
      exact ⟨E.1,E.2.trans (by norm_num [cell12789])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy18 (n := 12789) (by norm_num)
        (q := 1 - (cell12789 ⟨18,by decide⟩).lower)
        (by norm_num [cell12789]) (by norm_num [cell12789])
      exact ⟨E.1,E.2.trans (by norm_num [cell12789])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy19 (n := 12789) (by norm_num)
        (q := 1 - (cell12789 ⟨19,by decide⟩).lower)
        (by norm_num [cell12789]) (by norm_num [cell12789])
      exact ⟨E.1,E.2.trans (by norm_num [cell12789])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy20 (n := 12789) (by norm_num)
        (q := 1 - (cell12789 ⟨20,by decide⟩).lower)
        (by norm_num [cell12789]) (by norm_num [cell12789])
      exact ⟨E.1,E.2.trans (by norm_num [cell12789])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy21 (n := 12789) (by norm_num)
        (q := 1 - (cell12789 ⟨21,by decide⟩).lower)
        (by norm_num [cell12789]) (by norm_num [cell12789])
      exact ⟨E.1,E.2.trans (by norm_num [cell12789])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy22 (n := 12789) (by norm_num)
        (q := 1 - (cell12789 ⟨22,by decide⟩).lower)
        (by norm_num [cell12789]) (by norm_num [cell12789])
      exact ⟨E.1,E.2.trans (by norm_num [cell12789])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy23 (n := 12789) (by norm_num)
        (q := 1 - (cell12789 ⟨23,by decide⟩).lower)
        (by norm_num [cell12789]) (by norm_num [cell12789])
      exact ⟨E.1,E.2.trans (by norm_num [cell12789])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy24 (n := 12789) (by norm_num)
        (q := 1 - (cell12789 ⟨24,by decide⟩).lower)
        (by norm_num [cell12789]) (by norm_num [cell12789])
      exact ⟨E.1,E.2.trans (by norm_num [cell12789])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy25 (n := 12789) (by norm_num)
        (q := 1 - (cell12789 ⟨25,by decide⟩).lower)
        (by norm_num [cell12789]) (by norm_num [cell12789])
      exact ⟨E.1,E.2.trans (by norm_num [cell12789])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy26 (n := 12789) (by norm_num)
        (q := 1 - (cell12789 ⟨26,by decide⟩).lower)
        (by norm_num [cell12789]) (by norm_num [cell12789])
      exact ⟨E.1,E.2.trans (by norm_num [cell12789])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy27 (n := 12789) (by norm_num)
        (q := 1 - (cell12789 ⟨27,by decide⟩).lower)
        (by norm_num [cell12789]) (by norm_num [cell12789])
      exact ⟨E.1,E.2.trans (by norm_num [cell12789])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy28 (n := 12789) (by norm_num)
        (q := 1 - (cell12789 ⟨28,by decide⟩).lower)
        (by norm_num [cell12789]) (by norm_num [cell12789])
      exact ⟨E.1,E.2.trans (by norm_num [cell12789])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy29 (n := 12789) (by norm_num)
        (q := 1 - (cell12789 ⟨29,by decide⟩).lower)
        (by norm_num [cell12789]) (by norm_num [cell12789])
      exact ⟨E.1,E.2.trans (by norm_num [cell12789])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy30 (n := 12789) (by norm_num)
        (q := 1 - (cell12789 ⟨30,by decide⟩).lower)
        (by norm_num [cell12789]) (by norm_num [cell12789])
      exact ⟨E.1,E.2.trans (by norm_num [cell12789])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy31 (n := 12789) (by norm_num)
        (q := 1 - (cell12789 ⟨31,by decide⟩).lower)
        (by norm_num [cell12789]) (by norm_num [cell12789])
      exact ⟨E.1,E.2.trans (by norm_num [cell12789])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy32 (n := 12789) (by norm_num)
        (q := 1 - (cell12789 ⟨32,by decide⟩).lower)
        (by norm_num [cell12789]) (by norm_num [cell12789])
      exact ⟨E.1,E.2.trans (by norm_num [cell12789])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy33 (n := 12789) (by norm_num)
        (q := 1 - (cell12789 ⟨33,by decide⟩).lower)
        (by norm_num [cell12789]) (by norm_num [cell12789])
      exact ⟨E.1,E.2.trans (by norm_num [cell12789])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy34 (n := 12789) (by norm_num)
        (q := 1 - (cell12789 ⟨34,by decide⟩).lower)
        (by norm_num [cell12789]) (by norm_num [cell12789])
      exact ⟨E.1,E.2.trans (by norm_num [cell12789])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy35 (n := 12789) (by norm_num)
        (q := 1 - (cell12789 ⟨35,by decide⟩).lower)
        (by norm_num [cell12789]) (by norm_num [cell12789])
      exact ⟨E.1,E.2.trans (by norm_num [cell12789])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy36 (n := 12789) (by norm_num)
        (q := 1 - (cell12789 ⟨36,by decide⟩).lower)
        (by norm_num [cell12789]) (by norm_num [cell12789])
      exact ⟨E.1,E.2.trans (by norm_num [cell12789])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy37 (n := 12789) (by norm_num)
        (q := 1 - (cell12789 ⟨37,by decide⟩).lower)
        (by norm_num [cell12789]) (by norm_num [cell12789])
      exact ⟨E.1,E.2.trans (by norm_num [cell12789])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy38 (n := 12789) (by norm_num)
        (q := 1 - (cell12789 ⟨38,by decide⟩).lower)
        (by norm_num [cell12789]) (by norm_num [cell12789])
      exact ⟨E.1,E.2.trans (by norm_num [cell12789])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy39 (n := 12789) (by norm_num)
        (q := 1 - (cell12789 ⟨39,by decide⟩).lower)
        (by norm_num [cell12789]) (by norm_num [cell12789])
      exact ⟨E.1,E.2.trans (by norm_num [cell12789])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy40 (n := 12789) (by norm_num)
        (q := 1 - (cell12789 ⟨40,by decide⟩).lower)
        (by norm_num [cell12789]) (by norm_num [cell12789])
      exact ⟨E.1,E.2.trans (by norm_num [cell12789])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy41 (n := 12789) (by norm_num)
        (q := 1 - (cell12789 ⟨41,by decide⟩).lower)
        (by norm_num [cell12789]) (by norm_num [cell12789])
      exact ⟨E.1,E.2.trans (by norm_num [cell12789])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy42 (n := 12789) (by norm_num)
        (q := 1 - (cell12789 ⟨42,by decide⟩).lower)
        (by norm_num [cell12789]) (by norm_num [cell12789])
      exact ⟨E.1,E.2.trans (by norm_num [cell12789])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy43 (n := 12789) (by norm_num)
        (q := 1 - (cell12789 ⟨43,by decide⟩).lower)
        (by norm_num [cell12789]) (by norm_num [cell12789])
      exact ⟨E.1,E.2.trans (by norm_num [cell12789])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy44 (n := 12789) (by norm_num)
        (q := 1 - (cell12789 ⟨44,by decide⟩).lower)
        (by norm_num [cell12789]) (by norm_num [cell12789])
      exact ⟨E.1,E.2.trans (by norm_num [cell12789])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy45 (n := 12789) (by norm_num)
        (q := 1 - (cell12789 ⟨45,by decide⟩).lower)
        (by norm_num [cell12789]) (by norm_num [cell12789])
      exact ⟨E.1,E.2.trans (by norm_num [cell12789])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy46 (n := 12789) (by norm_num)
        (q := 1 - (cell12789 ⟨46,by decide⟩).lower)
        (by norm_num [cell12789]) (by norm_num [cell12789])
      exact ⟨E.1,E.2.trans (by norm_num [cell12789])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy47 (n := 12789) (by norm_num)
        (q := 1 - (cell12789 ⟨47,by decide⟩).lower)
        (by norm_num [cell12789]) (by norm_num [cell12789])
      exact ⟨E.1,E.2.trans (by norm_num [cell12789])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy48 (n := 12789) (by norm_num)
        (q := 1 - (cell12789 ⟨48,by decide⟩).lower)
        (by norm_num [cell12789]) (by norm_num [cell12789])
      exact ⟨E.1,E.2.trans (by norm_num [cell12789])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy49 (n := 12789) (by norm_num)
        (q := 1 - (cell12789 ⟨49,by decide⟩).lower)
        (by norm_num [cell12789]) (by norm_num [cell12789])
      exact ⟨E.1,E.2.trans (by norm_num [cell12789])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy50 (n := 12789) (by norm_num)
        (q := 1 - (cell12789 ⟨50,by decide⟩).lower)
        (by norm_num [cell12789]) (by norm_num [cell12789])
      exact ⟨E.1,E.2.trans (by norm_num [cell12789])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy51 (n := 12789) (by norm_num)
        (q := 1 - (cell12789 ⟨51,by decide⟩).lower)
        (by norm_num [cell12789]) (by norm_num [cell12789])
      exact ⟨E.1,E.2.trans (by norm_num [cell12789])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy52 (n := 12789) (by norm_num)
        (q := 1 - (cell12789 ⟨52,by decide⟩).lower)
        (by norm_num [cell12789]) (by norm_num [cell12789])
      exact ⟨E.1,E.2.trans (by norm_num [cell12789])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12789

/-! Source-cell containment and simple scalar guards at 12789. -/
namespace BstLean.Part269.N12789
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12789)
open BstLean.Part268 (cell12789)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12789 ⟨10,by decide⟩).lower ∧ (cell12789 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12789 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12789 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12789 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12789 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12789 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12789,cell12789,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12789 ⟨11,by decide⟩).lower ∧ (cell12789 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12789 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12789 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12789 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12789 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12789 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12789,cell12789,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12789 ⟨12,by decide⟩).lower ∧ (cell12789 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12789 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12789 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12789 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12789 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12789 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12789,cell12789,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12789 ⟨13,by decide⟩).lower ∧ (cell12789 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12789 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12789 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12789 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12789 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12789 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12789,cell12789,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12789 ⟨14,by decide⟩).lower ∧ (cell12789 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12789 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12789 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12789 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12789 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12789 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12789,cell12789,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12789 ⟨15,by decide⟩).lower ∧ (cell12789 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12789 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12789 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12789 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12789 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12789 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12789,cell12789,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12789 ⟨16,by decide⟩).lower ∧ (cell12789 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12789 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12789 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12789 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12789 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12789 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12789,cell12789,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12789 ⟨17,by decide⟩).lower ∧ (cell12789 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12789 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12789 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12789 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12789 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12789 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12789,cell12789,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12789 ⟨18,by decide⟩).lower ∧ (cell12789 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12789 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12789 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12789 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12789 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12789 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12789,cell12789,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12789 ⟨19,by decide⟩).lower ∧ (cell12789 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12789 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12789 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12789 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12789 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12789 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12789,cell12789,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12789 ⟨20,by decide⟩).lower ∧ (cell12789 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12789 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12789 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12789 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12789 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12789 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12789,cell12789,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12789 ⟨21,by decide⟩).lower ∧ (cell12789 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12789 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12789 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12789 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12789 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12789 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12789,cell12789,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12789 ⟨22,by decide⟩).lower ∧ (cell12789 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12789 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12789 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12789 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12789 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12789 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12789,cell12789,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12789 ⟨23,by decide⟩).lower ∧ (cell12789 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12789 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12789 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12789 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12789 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12789 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12789,cell12789,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12789 ⟨24,by decide⟩).lower ∧ (cell12789 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12789 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12789 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12789 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12789 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12789 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12789,cell12789,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12789 ⟨25,by decide⟩).lower ∧ (cell12789 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12789 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12789 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12789 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12789 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12789 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12789,cell12789,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12789 ⟨26,by decide⟩).lower ∧ (cell12789 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12789 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12789 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12789 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12789 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12789 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12789,cell12789,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12789 ⟨27,by decide⟩).lower ∧ (cell12789 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12789 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12789 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12789 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12789 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12789 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12789,cell12789,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12789 ⟨28,by decide⟩).lower ∧ (cell12789 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12789 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12789 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12789 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12789 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12789 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12789,cell12789,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12789 ⟨29,by decide⟩).lower ∧ (cell12789 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12789 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12789 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12789 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12789 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12789 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12789,cell12789,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12789 ⟨30,by decide⟩).lower ∧ (cell12789 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12789 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12789 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12789 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12789 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12789 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12789,cell12789,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12789 ⟨31,by decide⟩).lower ∧ (cell12789 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12789 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12789 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12789 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12789 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12789 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12789,cell12789,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12789 ⟨32,by decide⟩).lower ∧ (cell12789 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12789 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12789 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12789 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12789 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12789 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12789,cell12789,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12789 ⟨33,by decide⟩).lower ∧ (cell12789 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12789 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12789 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12789 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12789 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12789 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12789,cell12789,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12789 ⟨34,by decide⟩).lower ∧ (cell12789 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12789 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12789 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12789 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12789 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12789 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12789,cell12789,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12789 ⟨35,by decide⟩).lower ∧ (cell12789 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12789 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12789 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12789 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12789 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12789 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12789,cell12789,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12789 ⟨36,by decide⟩).lower ∧ (cell12789 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12789 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12789 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12789 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12789 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12789 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12789,cell12789,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12789 ⟨37,by decide⟩).lower ∧ (cell12789 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12789 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12789 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12789 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12789 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12789 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12789,cell12789,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12789 ⟨38,by decide⟩).lower ∧ (cell12789 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12789 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12789 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12789 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12789 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12789 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12789,cell12789,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12789 ⟨39,by decide⟩).lower ∧ (cell12789 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12789 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12789 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12789 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12789 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12789 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12789,cell12789,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12789 ⟨40,by decide⟩).lower ∧ (cell12789 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12789 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12789 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12789 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12789 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12789 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12789,cell12789,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12789 ⟨41,by decide⟩).lower ∧ (cell12789 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12789 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12789 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12789 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12789 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12789 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12789,cell12789,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12789 ⟨42,by decide⟩).lower ∧ (cell12789 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12789 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12789 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12789 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12789 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12789 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12789,cell12789,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12789 ⟨43,by decide⟩).lower ∧ (cell12789 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12789 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12789 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12789 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12789 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12789 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12789,cell12789,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12789 ⟨44,by decide⟩).lower ∧ (cell12789 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12789 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12789 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12789 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12789 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12789 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12789,cell12789,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12789 ⟨45,by decide⟩).lower ∧ (cell12789 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12789 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12789 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12789 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12789 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12789 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12789,cell12789,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12789 ⟨46,by decide⟩).lower ∧ (cell12789 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12789 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12789 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12789 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12789 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12789 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12789,cell12789,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12789 ⟨47,by decide⟩).lower ∧ (cell12789 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12789 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12789 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12789 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12789 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12789 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12789,cell12789,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12789 ⟨48,by decide⟩).lower ∧ (cell12789 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12789 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12789 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12789 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12789 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12789 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12789,cell12789,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12789 ⟨49,by decide⟩).lower ∧ (cell12789 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12789 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12789 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12789 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12789 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12789 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12789,cell12789,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12789 ⟨50,by decide⟩).lower ∧ (cell12789 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12789 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12789 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12789 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12789 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12789 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12789,cell12789,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12789 ⟨51,by decide⟩).lower ∧ (cell12789 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12789 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12789 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12789 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12789 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12789 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12789,cell12789,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12789 ⟨52,by decide⟩).lower ∧ (cell12789 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12789 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12789 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12789 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12789 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12789 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12789,cell12789,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12789 i).lower ∧
    (cell12789 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12789 i).upper ≤ (0.532 : ℝ) ∧
    (cell12789 i).centre ≤ (0.1 : ℝ) ∧ (cell12789 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12789 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12789 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12789

/-! The local source numeric instances at 12789 have no network premises. -/
namespace BstLean.Part269.N12789
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12789)
open BstLean.Part268 (cell12789)

noncomputable def sourceNumerics12789 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12789 (cell12789 i)
      scalarRow12789.M scalarRow12789.H scalarRow12789.xi := by
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
    energy_allowance := scalarRow12789.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12789]
    centre_nonneg := (scalarRow12789.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D17.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12789])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12789
/-! Actual 12790 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12790
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12790 ≤ (1.035681902168 : ℝ) := by
  have hr : (113.092882180975 : ℝ) ≤ √(12790 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.092882180975 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12790 12790 (11 / 1000) ≤
    (0.008452229573 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12790) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.092882180975 : ℝ) ≤ √(12790 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12790)
  have hdiv : K / √(12790 : ℝ) ≤ K / 113.092882180975 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.092882180975 ≤ (0.008452229573 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12790.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12790 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12790 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12790 := gPlus_lower 12790
end BstLean.Part269.N12790

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12790
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035681902167 : ℝ) ≤ wn 12790 := by
  have hn : √(12790 : ℝ) ≤ 113.092882180976 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12790 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.092882180976 ≤ 2 / √(12790 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000250077704 : ℝ) ≤ rhoBar 12790 BstLean.Part154.csC ∧
    rhoBar 12790 BstLean.Part154.csC ≤ 0.000250078091 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035681902167 : ℝ) / (1.295212 * 12790) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035681902168 : ℝ) / (1.29521 * 12790) := by gcongr
      _ ≤ (0.000250078091 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12790 BstLean.Part154.csC) ≤ 0.001000374904 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12790 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12790 BstLean.Part154.csC) (piBar (rhoBar 12790 BstLean.Part154.csC)) ≤ 0.000191011269 ∧
    cc1 (rhoBar 12790 BstLean.Part154.csC) (piBar (rhoBar 12790 BstLean.Part154.csC)) ≤ 0.000121541752 ∧
    cc2 (rhoBar 12790 BstLean.Part154.csC) ≤ 0.000070555934 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12790 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12790 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12790 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12790 BstLean.Part154.csC * nuR (rhoBar 12790 BstLean.Part154.csC)) ≤ 0.000500171817 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000250078091 : ℝ) * 0.001000374904 := by gcongr
      _ ≤ (0.000500171817 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12790 BstLean.Part154.csC) * nuR (rhoBar 12790 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001000374904 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12790 BstLean.Part154.csC) * rhoBar 12790 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000250078091 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000250078091 / 2 + 0.399 * 0.001000374904 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000191011269 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000500171817 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121541752 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000250078091 / 1.414213562 := by gcongr
      _ ≤ (0.000070555934 : ℝ) := by norm_num

end BstLean.Part269.N12790

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12790
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12790 BstLean.Part154.csC) (piBar (rhoBar 12790 BstLean.Part154.csC)) ≤ 1.57563E-7 := by
  have hr0 : 0 ≤ rhoBar 12790 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12790 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12790 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12790 BstLean.Part154.csC) (piBar (rhoBar 12790 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12790 BstLean.Part154.csC) (piBar (rhoBar 12790 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12790 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000191011269 : ℝ) ^ 2 + 0.000121541752 ^ 2 + 3 * 0.000070555934 ^ 2 +
        2 * 0.797885 * 0.000191011269 * 0.000121541752 + 2 * 0.000191011269 * 0.000070555934 +
        4 * 0.797885 * 0.000121541752 * 0.000070555934 := by gcongr
    _ ≤ (1.57563E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12790 BstLean.Part154.csC Θ ≤ 0.002610151085 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12790 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12790 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12790 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12790 BstLean.Part154.csC) (piBar (rhoBar 12790 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12790 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035681902168 * 1.57563E-7 / (0.000250077704 : ℝ) := by gcongr
    _ ≤ 0.002610151085 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12790 BstLean.Part154.csC Θ ≤ 0.002895740054 + 0.000659541667 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12790 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12790 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12790 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035681902168 : ℝ) * ((2 * Θ * 0.000250078091 +
        (6863 / 10000) * 0.000250078091 * 12790 * 0.001000374904) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002895740054 + 0.000659541667 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12790 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12790 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12790 0.011 Θ ∧ gammaRatio 12790 0.011 Θ ≤ 0.000085970381 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12790 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035681902168 : ℝ) * 0.525 / ((1 - 0.011) * 12790) := by gcongr
      _ ≤ (0.000085970381 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12790 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12790 0.011 Θ) :=
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
    badAllowance 12790 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000560204559 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12790 BstLean.Part154.csC) 1.22 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 2 (rhoBar 12790 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12790 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12790 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12790 0.011 Θ) 1.12 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 1 (gammaRatio 12790 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12790 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12790 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12790 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12790 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035681902168 : ℝ) * 12790 *
        (1.8602E-8 / 1.1045361 + 2.2721E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000560204559 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12790 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003455944613 + 0.003269692752 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12790

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12790
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12790 BstLean.Part154.csC) (piBar (rhoBar 12790 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12790 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12790 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12790 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12790 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12790 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12790 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12790 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12790 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12790 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12790 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12790 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12790 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12790 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12790 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052297328558 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12790) ≤ 0.010559794375 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12790 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035681902168)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010559794375 + 2 * 0.737676 / 12790) := by gcongr
    _ ≤ (0.052297328558 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12790 12 ≤ 0.0015 := by
  exact BstLean.Part269.S17.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12790

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12790
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560507609718 : ℝ) ≤ plow 12790 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12790) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052679133308)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001370329320) : eMP 12790 0.011 xi bn ≤ 0.001179850099 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12790 : ℝ) * (1 - 0.011))) ≤ 0.000583383333 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001370329320 / (12790 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000583383333 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000583383333 : ℝ) + 3.141593 * 0.052679133308 / (12790 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001179850099 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052679133308)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001370329320) : PiBarMP 12790 12 0.011 xi bn ≤ 0.160677139855 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12790 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037017959426 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.469151326041 : ℝ) ≤ √((12790 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.092882180975 : ℝ) ≤ √(12790 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12790) ≤ 0.123194386721 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037017959426 + 0.052679133308 * 1.772454 / (2 * (112.469151326041 : ℝ))) * (1 + 0.001179850099) +
        8 / (12790 * 113.092882180975) + 0.123194386721 := by gcongr
    _ ≤ (0.160677139855 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052679133308)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001370329320) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281816681355) :
    parallelOracle 12790 0.011 xi bn cd ≤ 0.161660759347 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12790 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12790 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560507609718 : ℝ) ≤ plow 12790 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.092882180975 : ℝ) ≤ √(12790 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281816681355 : ℝ) / (2 * 0.560507609718 * 113.092882180975)) * 0.160677139855 +
        0.281816681355 ^ 2 / (2 * 0.560507609718 * 113.092882180975) := by gcongr
    _ ≤ (0.161660759347 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052679133308) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001370329320)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281816681355) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12790 12790 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560507609718 : ℝ) ≤ plow 12790 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.092882180975 : ℝ) ≤ √(12790 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12790 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12790 Θ 1.22 ≤ 0.011725764473 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.092882180975 := by gcongr <;> linarith
      _ ≤ (0.011725764473 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12790 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12790 12790 0.011 ≤ 0.008452229573 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12790 12790 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12790 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12790 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12790 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12790 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161660759347 + 0.011725764473 + (0.008452229573 : ℝ) *
        (1 + 2 * (0.281816681355 + 0.011725764473) / (0.560507609718 * 113.092882180975))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12790]

end BstLean.Part269.N12790

/-! The original eight local profiles supply actual 12790 moment certificates. -/
namespace BstLean.Part269.N12790
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12790 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12790 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12790 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052679133308 ∧
    0 ≤ bN 12790 BstLean.Part154.csC (groupTheta g) ∧ bN 12790 BstLean.Part154.csC (groupTheta g) ≤ 0.001370329320 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12790 12790 0.011
      (momentAllowance 12790 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12790 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12790 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12790 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12790 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12790 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229519352797 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12790 0.011
      (momentAllowance 12790 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12790 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12790
/-! The actual computed-centre upper energy formula at 12790. -/
namespace BstLean.Part269.N12790
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12790

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12790
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12790)
open BstLean.Part268 (cell12790)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085232050054
  | 2 => 0.086170150628
  | 3 => 0.087105728140
  | 4 => 0.088040046917
  | 5 => 0.088974641128
  | 6 => 0.089911355487
  | 7 => 0.090852389908
  | 8 => 0.091800348169
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12790 12790 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12790 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003459522332 + 0.003273654356 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S17.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12790

/-! Actual upper energy certificates on all 43 source endpoints at 12790. -/
namespace BstLean.Part269.N12790
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12790)
open BstLean.Part268 (cell12790)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12790 (gMinus 12790) (1 - (cell12790 i).lower) ≤ 1 ∧
    energyUpper 12790 (gMinus 12790) (BstLean.Part211.gPlus 12790)
      (finiteEnergy 12790 12790 0.011) (1 - (cell12790 i).lower) ≤
      (cell12790 i).energy := by
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
      have E := BstLean.Part269.S17.uniformEnergy10 (n := 12790) (by norm_num)
        (q := 1 - (cell12790 ⟨10,by decide⟩).lower)
        (by norm_num [cell12790]) (by norm_num [cell12790])
      exact ⟨E.1,E.2.trans (by norm_num [cell12790])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy11 (n := 12790) (by norm_num)
        (q := 1 - (cell12790 ⟨11,by decide⟩).lower)
        (by norm_num [cell12790]) (by norm_num [cell12790])
      exact ⟨E.1,E.2.trans (by norm_num [cell12790])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy12 (n := 12790) (by norm_num)
        (q := 1 - (cell12790 ⟨12,by decide⟩).lower)
        (by norm_num [cell12790]) (by norm_num [cell12790])
      exact ⟨E.1,E.2.trans (by norm_num [cell12790])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy13 (n := 12790) (by norm_num)
        (q := 1 - (cell12790 ⟨13,by decide⟩).lower)
        (by norm_num [cell12790]) (by norm_num [cell12790])
      exact ⟨E.1,E.2.trans (by norm_num [cell12790])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy14 (n := 12790) (by norm_num)
        (q := 1 - (cell12790 ⟨14,by decide⟩).lower)
        (by norm_num [cell12790]) (by norm_num [cell12790])
      exact ⟨E.1,E.2.trans (by norm_num [cell12790])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy15 (n := 12790) (by norm_num)
        (q := 1 - (cell12790 ⟨15,by decide⟩).lower)
        (by norm_num [cell12790]) (by norm_num [cell12790])
      exact ⟨E.1,E.2.trans (by norm_num [cell12790])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy16 (n := 12790) (by norm_num)
        (q := 1 - (cell12790 ⟨16,by decide⟩).lower)
        (by norm_num [cell12790]) (by norm_num [cell12790])
      exact ⟨E.1,E.2.trans (by norm_num [cell12790])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy17 (n := 12790) (by norm_num)
        (q := 1 - (cell12790 ⟨17,by decide⟩).lower)
        (by norm_num [cell12790]) (by norm_num [cell12790])
      exact ⟨E.1,E.2.trans (by norm_num [cell12790])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy18 (n := 12790) (by norm_num)
        (q := 1 - (cell12790 ⟨18,by decide⟩).lower)
        (by norm_num [cell12790]) (by norm_num [cell12790])
      exact ⟨E.1,E.2.trans (by norm_num [cell12790])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy19 (n := 12790) (by norm_num)
        (q := 1 - (cell12790 ⟨19,by decide⟩).lower)
        (by norm_num [cell12790]) (by norm_num [cell12790])
      exact ⟨E.1,E.2.trans (by norm_num [cell12790])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy20 (n := 12790) (by norm_num)
        (q := 1 - (cell12790 ⟨20,by decide⟩).lower)
        (by norm_num [cell12790]) (by norm_num [cell12790])
      exact ⟨E.1,E.2.trans (by norm_num [cell12790])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy21 (n := 12790) (by norm_num)
        (q := 1 - (cell12790 ⟨21,by decide⟩).lower)
        (by norm_num [cell12790]) (by norm_num [cell12790])
      exact ⟨E.1,E.2.trans (by norm_num [cell12790])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy22 (n := 12790) (by norm_num)
        (q := 1 - (cell12790 ⟨22,by decide⟩).lower)
        (by norm_num [cell12790]) (by norm_num [cell12790])
      exact ⟨E.1,E.2.trans (by norm_num [cell12790])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy23 (n := 12790) (by norm_num)
        (q := 1 - (cell12790 ⟨23,by decide⟩).lower)
        (by norm_num [cell12790]) (by norm_num [cell12790])
      exact ⟨E.1,E.2.trans (by norm_num [cell12790])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy24 (n := 12790) (by norm_num)
        (q := 1 - (cell12790 ⟨24,by decide⟩).lower)
        (by norm_num [cell12790]) (by norm_num [cell12790])
      exact ⟨E.1,E.2.trans (by norm_num [cell12790])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy25 (n := 12790) (by norm_num)
        (q := 1 - (cell12790 ⟨25,by decide⟩).lower)
        (by norm_num [cell12790]) (by norm_num [cell12790])
      exact ⟨E.1,E.2.trans (by norm_num [cell12790])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy26 (n := 12790) (by norm_num)
        (q := 1 - (cell12790 ⟨26,by decide⟩).lower)
        (by norm_num [cell12790]) (by norm_num [cell12790])
      exact ⟨E.1,E.2.trans (by norm_num [cell12790])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy27 (n := 12790) (by norm_num)
        (q := 1 - (cell12790 ⟨27,by decide⟩).lower)
        (by norm_num [cell12790]) (by norm_num [cell12790])
      exact ⟨E.1,E.2.trans (by norm_num [cell12790])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy28 (n := 12790) (by norm_num)
        (q := 1 - (cell12790 ⟨28,by decide⟩).lower)
        (by norm_num [cell12790]) (by norm_num [cell12790])
      exact ⟨E.1,E.2.trans (by norm_num [cell12790])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy29 (n := 12790) (by norm_num)
        (q := 1 - (cell12790 ⟨29,by decide⟩).lower)
        (by norm_num [cell12790]) (by norm_num [cell12790])
      exact ⟨E.1,E.2.trans (by norm_num [cell12790])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy30 (n := 12790) (by norm_num)
        (q := 1 - (cell12790 ⟨30,by decide⟩).lower)
        (by norm_num [cell12790]) (by norm_num [cell12790])
      exact ⟨E.1,E.2.trans (by norm_num [cell12790])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy31 (n := 12790) (by norm_num)
        (q := 1 - (cell12790 ⟨31,by decide⟩).lower)
        (by norm_num [cell12790]) (by norm_num [cell12790])
      exact ⟨E.1,E.2.trans (by norm_num [cell12790])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy32 (n := 12790) (by norm_num)
        (q := 1 - (cell12790 ⟨32,by decide⟩).lower)
        (by norm_num [cell12790]) (by norm_num [cell12790])
      exact ⟨E.1,E.2.trans (by norm_num [cell12790])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy33 (n := 12790) (by norm_num)
        (q := 1 - (cell12790 ⟨33,by decide⟩).lower)
        (by norm_num [cell12790]) (by norm_num [cell12790])
      exact ⟨E.1,E.2.trans (by norm_num [cell12790])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy34 (n := 12790) (by norm_num)
        (q := 1 - (cell12790 ⟨34,by decide⟩).lower)
        (by norm_num [cell12790]) (by norm_num [cell12790])
      exact ⟨E.1,E.2.trans (by norm_num [cell12790])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy35 (n := 12790) (by norm_num)
        (q := 1 - (cell12790 ⟨35,by decide⟩).lower)
        (by norm_num [cell12790]) (by norm_num [cell12790])
      exact ⟨E.1,E.2.trans (by norm_num [cell12790])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy36 (n := 12790) (by norm_num)
        (q := 1 - (cell12790 ⟨36,by decide⟩).lower)
        (by norm_num [cell12790]) (by norm_num [cell12790])
      exact ⟨E.1,E.2.trans (by norm_num [cell12790])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy37 (n := 12790) (by norm_num)
        (q := 1 - (cell12790 ⟨37,by decide⟩).lower)
        (by norm_num [cell12790]) (by norm_num [cell12790])
      exact ⟨E.1,E.2.trans (by norm_num [cell12790])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy38 (n := 12790) (by norm_num)
        (q := 1 - (cell12790 ⟨38,by decide⟩).lower)
        (by norm_num [cell12790]) (by norm_num [cell12790])
      exact ⟨E.1,E.2.trans (by norm_num [cell12790])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy39 (n := 12790) (by norm_num)
        (q := 1 - (cell12790 ⟨39,by decide⟩).lower)
        (by norm_num [cell12790]) (by norm_num [cell12790])
      exact ⟨E.1,E.2.trans (by norm_num [cell12790])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy40 (n := 12790) (by norm_num)
        (q := 1 - (cell12790 ⟨40,by decide⟩).lower)
        (by norm_num [cell12790]) (by norm_num [cell12790])
      exact ⟨E.1,E.2.trans (by norm_num [cell12790])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy41 (n := 12790) (by norm_num)
        (q := 1 - (cell12790 ⟨41,by decide⟩).lower)
        (by norm_num [cell12790]) (by norm_num [cell12790])
      exact ⟨E.1,E.2.trans (by norm_num [cell12790])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy42 (n := 12790) (by norm_num)
        (q := 1 - (cell12790 ⟨42,by decide⟩).lower)
        (by norm_num [cell12790]) (by norm_num [cell12790])
      exact ⟨E.1,E.2.trans (by norm_num [cell12790])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy43 (n := 12790) (by norm_num)
        (q := 1 - (cell12790 ⟨43,by decide⟩).lower)
        (by norm_num [cell12790]) (by norm_num [cell12790])
      exact ⟨E.1,E.2.trans (by norm_num [cell12790])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy44 (n := 12790) (by norm_num)
        (q := 1 - (cell12790 ⟨44,by decide⟩).lower)
        (by norm_num [cell12790]) (by norm_num [cell12790])
      exact ⟨E.1,E.2.trans (by norm_num [cell12790])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy45 (n := 12790) (by norm_num)
        (q := 1 - (cell12790 ⟨45,by decide⟩).lower)
        (by norm_num [cell12790]) (by norm_num [cell12790])
      exact ⟨E.1,E.2.trans (by norm_num [cell12790])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy46 (n := 12790) (by norm_num)
        (q := 1 - (cell12790 ⟨46,by decide⟩).lower)
        (by norm_num [cell12790]) (by norm_num [cell12790])
      exact ⟨E.1,E.2.trans (by norm_num [cell12790])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy47 (n := 12790) (by norm_num)
        (q := 1 - (cell12790 ⟨47,by decide⟩).lower)
        (by norm_num [cell12790]) (by norm_num [cell12790])
      exact ⟨E.1,E.2.trans (by norm_num [cell12790])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy48 (n := 12790) (by norm_num)
        (q := 1 - (cell12790 ⟨48,by decide⟩).lower)
        (by norm_num [cell12790]) (by norm_num [cell12790])
      exact ⟨E.1,E.2.trans (by norm_num [cell12790])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy49 (n := 12790) (by norm_num)
        (q := 1 - (cell12790 ⟨49,by decide⟩).lower)
        (by norm_num [cell12790]) (by norm_num [cell12790])
      exact ⟨E.1,E.2.trans (by norm_num [cell12790])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy50 (n := 12790) (by norm_num)
        (q := 1 - (cell12790 ⟨50,by decide⟩).lower)
        (by norm_num [cell12790]) (by norm_num [cell12790])
      exact ⟨E.1,E.2.trans (by norm_num [cell12790])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy51 (n := 12790) (by norm_num)
        (q := 1 - (cell12790 ⟨51,by decide⟩).lower)
        (by norm_num [cell12790]) (by norm_num [cell12790])
      exact ⟨E.1,E.2.trans (by norm_num [cell12790])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy52 (n := 12790) (by norm_num)
        (q := 1 - (cell12790 ⟨52,by decide⟩).lower)
        (by norm_num [cell12790]) (by norm_num [cell12790])
      exact ⟨E.1,E.2.trans (by norm_num [cell12790])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12790

/-! Source-cell containment and simple scalar guards at 12790. -/
namespace BstLean.Part269.N12790
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12790)
open BstLean.Part268 (cell12790)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12790 ⟨10,by decide⟩).lower ∧ (cell12790 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12790 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12790 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12790 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12790 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12790 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12790,cell12790,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12790 ⟨11,by decide⟩).lower ∧ (cell12790 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12790 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12790 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12790 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12790 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12790 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12790,cell12790,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12790 ⟨12,by decide⟩).lower ∧ (cell12790 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12790 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12790 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12790 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12790 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12790 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12790,cell12790,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12790 ⟨13,by decide⟩).lower ∧ (cell12790 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12790 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12790 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12790 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12790 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12790 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12790,cell12790,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12790 ⟨14,by decide⟩).lower ∧ (cell12790 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12790 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12790 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12790 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12790 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12790 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12790,cell12790,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12790 ⟨15,by decide⟩).lower ∧ (cell12790 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12790 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12790 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12790 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12790 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12790 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12790,cell12790,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12790 ⟨16,by decide⟩).lower ∧ (cell12790 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12790 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12790 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12790 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12790 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12790 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12790,cell12790,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12790 ⟨17,by decide⟩).lower ∧ (cell12790 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12790 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12790 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12790 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12790 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12790 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12790,cell12790,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12790 ⟨18,by decide⟩).lower ∧ (cell12790 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12790 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12790 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12790 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12790 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12790 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12790,cell12790,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12790 ⟨19,by decide⟩).lower ∧ (cell12790 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12790 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12790 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12790 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12790 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12790 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12790,cell12790,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12790 ⟨20,by decide⟩).lower ∧ (cell12790 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12790 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12790 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12790 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12790 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12790 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12790,cell12790,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12790 ⟨21,by decide⟩).lower ∧ (cell12790 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12790 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12790 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12790 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12790 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12790 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12790,cell12790,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12790 ⟨22,by decide⟩).lower ∧ (cell12790 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12790 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12790 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12790 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12790 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12790 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12790,cell12790,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12790 ⟨23,by decide⟩).lower ∧ (cell12790 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12790 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12790 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12790 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12790 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12790 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12790,cell12790,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12790 ⟨24,by decide⟩).lower ∧ (cell12790 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12790 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12790 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12790 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12790 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12790 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12790,cell12790,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12790 ⟨25,by decide⟩).lower ∧ (cell12790 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12790 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12790 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12790 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12790 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12790 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12790,cell12790,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12790 ⟨26,by decide⟩).lower ∧ (cell12790 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12790 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12790 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12790 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12790 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12790 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12790,cell12790,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12790 ⟨27,by decide⟩).lower ∧ (cell12790 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12790 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12790 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12790 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12790 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12790 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12790,cell12790,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12790 ⟨28,by decide⟩).lower ∧ (cell12790 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12790 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12790 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12790 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12790 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12790 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12790,cell12790,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12790 ⟨29,by decide⟩).lower ∧ (cell12790 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12790 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12790 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12790 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12790 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12790 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12790,cell12790,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12790 ⟨30,by decide⟩).lower ∧ (cell12790 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12790 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12790 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12790 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12790 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12790 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12790,cell12790,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12790 ⟨31,by decide⟩).lower ∧ (cell12790 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12790 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12790 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12790 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12790 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12790 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12790,cell12790,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12790 ⟨32,by decide⟩).lower ∧ (cell12790 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12790 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12790 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12790 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12790 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12790 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12790,cell12790,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12790 ⟨33,by decide⟩).lower ∧ (cell12790 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12790 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12790 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12790 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12790 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12790 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12790,cell12790,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12790 ⟨34,by decide⟩).lower ∧ (cell12790 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12790 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12790 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12790 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12790 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12790 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12790,cell12790,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12790 ⟨35,by decide⟩).lower ∧ (cell12790 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12790 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12790 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12790 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12790 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12790 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12790,cell12790,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12790 ⟨36,by decide⟩).lower ∧ (cell12790 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12790 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12790 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12790 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12790 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12790 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12790,cell12790,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12790 ⟨37,by decide⟩).lower ∧ (cell12790 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12790 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12790 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12790 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12790 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12790 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12790,cell12790,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12790 ⟨38,by decide⟩).lower ∧ (cell12790 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12790 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12790 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12790 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12790 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12790 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12790,cell12790,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12790 ⟨39,by decide⟩).lower ∧ (cell12790 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12790 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12790 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12790 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12790 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12790 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12790,cell12790,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12790 ⟨40,by decide⟩).lower ∧ (cell12790 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12790 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12790 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12790 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12790 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12790 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12790,cell12790,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12790 ⟨41,by decide⟩).lower ∧ (cell12790 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12790 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12790 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12790 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12790 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12790 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12790,cell12790,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12790 ⟨42,by decide⟩).lower ∧ (cell12790 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12790 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12790 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12790 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12790 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12790 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12790,cell12790,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12790 ⟨43,by decide⟩).lower ∧ (cell12790 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12790 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12790 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12790 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12790 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12790 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12790,cell12790,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12790 ⟨44,by decide⟩).lower ∧ (cell12790 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12790 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12790 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12790 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12790 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12790 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12790,cell12790,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12790 ⟨45,by decide⟩).lower ∧ (cell12790 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12790 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12790 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12790 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12790 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12790 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12790,cell12790,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12790 ⟨46,by decide⟩).lower ∧ (cell12790 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12790 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12790 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12790 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12790 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12790 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12790,cell12790,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12790 ⟨47,by decide⟩).lower ∧ (cell12790 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12790 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12790 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12790 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12790 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12790 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12790,cell12790,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12790 ⟨48,by decide⟩).lower ∧ (cell12790 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12790 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12790 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12790 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12790 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12790 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12790,cell12790,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12790 ⟨49,by decide⟩).lower ∧ (cell12790 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12790 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12790 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12790 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12790 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12790 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12790,cell12790,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12790 ⟨50,by decide⟩).lower ∧ (cell12790 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12790 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12790 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12790 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12790 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12790 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12790,cell12790,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12790 ⟨51,by decide⟩).lower ∧ (cell12790 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12790 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12790 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12790 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12790 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12790 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12790,cell12790,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12790 ⟨52,by decide⟩).lower ∧ (cell12790 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12790 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12790 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12790 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12790 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12790 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12790,cell12790,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12790 i).lower ∧
    (cell12790 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12790 i).upper ≤ (0.532 : ℝ) ∧
    (cell12790 i).centre ≤ (0.1 : ℝ) ∧ (cell12790 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12790 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12790 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12790

/-! The local source numeric instances at 12790 have no network premises. -/
namespace BstLean.Part269.N12790
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12790)
open BstLean.Part268 (cell12790)

noncomputable def sourceNumerics12790 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12790 (cell12790 i)
      scalarRow12790.M scalarRow12790.H scalarRow12790.xi := by
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
    energy_allowance := scalarRow12790.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12790]
    centre_nonneg := (scalarRow12790.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D17.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12790])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12790
/-! Actual 12791 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12791
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12791 ≤ (1.035680495111 : ℝ) := by
  have hr : (113.097303239290 : ℝ) ≤ √(12791 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.097303239290 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12791 12791 (11 / 1000) ≤
    (0.008451899166 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12791) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.097303239290 : ℝ) ≤ √(12791 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12791)
  have hdiv : K / √(12791 : ℝ) ≤ K / 113.097303239290 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.097303239290 ≤ (0.008451899166 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12791.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12791 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12791 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12791 := gPlus_lower 12791
end BstLean.Part269.N12791

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12791
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035680495110 : ℝ) ≤ wn 12791 := by
  have hn : √(12791 : ℝ) ≤ 113.097303239291 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12791 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.097303239291 ≤ 2 / √(12791 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000250057813 : ℝ) ≤ rhoBar 12791 BstLean.Part154.csC ∧
    rhoBar 12791 BstLean.Part154.csC ≤ 0.000250058201 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035680495110 : ℝ) / (1.295212 * 12791) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035680495111 : ℝ) / (1.29521 * 12791) := by gcongr
      _ ≤ (0.000250058201 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12791 BstLean.Part154.csC) ≤ 0.001000295334 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12791 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12791 BstLean.Part154.csC) (piBar (rhoBar 12791 BstLean.Part154.csC)) ≤ 0.000190996077 ∧
    cc1 (rhoBar 12791 BstLean.Part154.csC) (piBar (rhoBar 12791 BstLean.Part154.csC)) ≤ 0.000121532085 ∧
    cc2 (rhoBar 12791 BstLean.Part154.csC) ≤ 0.000070550323 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12791 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12791 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12791 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12791 BstLean.Part154.csC * nuR (rhoBar 12791 BstLean.Part154.csC)) ≤ 0.000500132035 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000250058201 : ℝ) * 0.001000295334 := by gcongr
      _ ≤ (0.000500132035 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12791 BstLean.Part154.csC) * nuR (rhoBar 12791 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001000295334 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12791 BstLean.Part154.csC) * rhoBar 12791 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000250058201 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000250058201 / 2 + 0.399 * 0.001000295334 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000190996077 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000500132035 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121532085 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000250058201 / 1.414213562 := by gcongr
      _ ≤ (0.000070550323 : ℝ) := by norm_num

end BstLean.Part269.N12791

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12791
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12791 BstLean.Part154.csC) (piBar (rhoBar 12791 BstLean.Part154.csC)) ≤ 1.57538E-7 := by
  have hr0 : 0 ≤ rhoBar 12791 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12791 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12791 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12791 BstLean.Part154.csC) (piBar (rhoBar 12791 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12791 BstLean.Part154.csC) (piBar (rhoBar 12791 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12791 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000190996077 : ℝ) ^ 2 + 0.000121532085 ^ 2 + 3 * 0.000070550323 ^ 2 +
        2 * 0.797885 * 0.000190996077 * 0.000121532085 + 2 * 0.000190996077 * 0.000070550323 +
        4 * 0.797885 * 0.000121532085 * 0.000070550323 := by gcongr
    _ ≤ (1.57538E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12791 BstLean.Part154.csC Θ ≤ 0.002609940988 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12791 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12791 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12791 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12791 BstLean.Part154.csC) (piBar (rhoBar 12791 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12791 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035680495111 * 1.57538E-7 / (0.000250057813 : ℝ) := by gcongr
    _ ≤ 0.002609940988 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12791 BstLean.Part154.csC Θ ≤ 0.002895501869 + 0.000659488314 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12791 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12791 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12791 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035680495111 : ℝ) * ((2 * Θ * 0.000250058201 +
        (6863 / 10000) * 0.000250058201 * 12791 * 0.001000295334) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002895501869 + 0.000659488314 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12791 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12791 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12791 0.011 Θ ∧ gammaRatio 12791 0.011 Θ ≤ 0.000085963543 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12791 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035680495111 : ℝ) * 0.525 / ((1 - 0.011) * 12791) := by gcongr
      _ ≤ (0.000085963543 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12791 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12791 0.011 Θ) :=
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
    badAllowance 12791 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000560204559 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12791 BstLean.Part154.csC) 1.22 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 2 (rhoBar 12791 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12791 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12791 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12791 0.011 Θ) 1.12 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 1 (gammaRatio 12791 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12791 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12791 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12791 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12791 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035680495111 : ℝ) * 12791 *
        (1.8602E-8 / 1.1045361 + 2.2721E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000560204559 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12791 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003455706428 + 0.003269429302 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12791

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12791
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12791 BstLean.Part154.csC) (piBar (rhoBar 12791 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12791 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12791 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12791 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12791 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12791 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12791 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12791 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12791 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12791 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12791 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12791 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12791 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12791 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12791 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052295262128 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12791) ≤ 0.010559381585 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12791 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035680495111)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010559381585 + 2 * 0.737676 / 12791) := by gcongr
    _ ≤ (0.052295262128 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12791 12 ≤ 0.0015 := by
  exact BstLean.Part269.S17.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12791

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12791
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560507654303 : ℝ) ≤ plow 12791 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12791) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052678756812)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001370219019) : eMP 12791 0.011 xi bn ≤ 0.001179756417 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12791 : ℝ) * (1 - 0.011))) ≤ 0.000583337050 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001370219019 / (12791 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000583337050 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000583337050 : ℝ) + 3.141593 * 0.052678756812 / (12791 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001179756417 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052678756812)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001370219019) : PiBarMP 12791 12 0.011 xi bn ≤ 0.160670809104 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12791 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037016469565 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.473548001296 : ℝ) ≤ √((12791 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.097303239290 : ℝ) ≤ √(12791 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12791) ≤ 0.123189570960 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037016469565 + 0.052678756812 * 1.772454 / (2 * (112.473548001296 : ℝ))) * (1 + 0.001179756417) +
        8 / (12791 * 113.097303239290) + 0.123189570960 := by gcongr
    _ ≤ (0.160670809104 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052678756812)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001370219019) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281813794740) :
    parallelOracle 12791 0.011 xi bn cd ≤ 0.161654359504 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12791 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12791 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560507654303 : ℝ) ≤ plow 12791 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.097303239290 : ℝ) ≤ √(12791 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281813794740 : ℝ) / (2 * 0.560507654303 * 113.097303239290)) * 0.160670809104 +
        0.281813794740 ^ 2 / (2 * 0.560507654303 * 113.097303239290) := by gcongr
    _ ≤ (0.161654359504 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052678756812) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001370219019)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281813794740) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12791 12791 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560507654303 : ℝ) ≤ plow 12791 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.097303239290 : ℝ) ≤ √(12791 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12791 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12791 Θ 1.22 ≤ 0.011725306104 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.097303239290 := by gcongr <;> linarith
      _ ≤ (0.011725306104 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12791 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12791 12791 0.011 ≤ 0.008451899166 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12791 12791 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12791 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12791 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12791 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12791 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161654359504 + 0.011725306104 + (0.008451899166 : ℝ) *
        (1 + 2 * (0.281813794740 + 0.011725306104) / (0.560507654303 * 113.097303239290))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12791]

end BstLean.Part269.N12791

/-! The original eight local profiles supply actual 12791 moment certificates. -/
namespace BstLean.Part269.N12791
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12791 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12791 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12791 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052678756812 ∧
    0 ≤ bN 12791 BstLean.Part154.csC (groupTheta g) ∧ bN 12791 BstLean.Part154.csC (groupTheta g) ≤ 0.001370219019 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12791 12791 0.011
      (momentAllowance 12791 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12791 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12791 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12791 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12791 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12791 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229518532612 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12791 0.011
      (momentAllowance 12791 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12791 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12791
/-! The actual computed-centre upper energy formula at 12791. -/
namespace BstLean.Part269.N12791
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12791

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12791
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12791)
open BstLean.Part268 (cell12791)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085229227530
  | 2 => 0.086167278325
  | 3 => 0.087102799135
  | 4 => 0.088037052669
  | 5 => 0.088971571190
  | 6 => 0.089908197176
  | 7 => 0.090849127945
  | 8 => 0.091796964266
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12791 12791 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12791 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003459522332 + 0.003273654356 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S17.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12791

/-! Actual upper energy certificates on all 43 source endpoints at 12791. -/
namespace BstLean.Part269.N12791
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12791)
open BstLean.Part268 (cell12791)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12791 (gMinus 12791) (1 - (cell12791 i).lower) ≤ 1 ∧
    energyUpper 12791 (gMinus 12791) (BstLean.Part211.gPlus 12791)
      (finiteEnergy 12791 12791 0.011) (1 - (cell12791 i).lower) ≤
      (cell12791 i).energy := by
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
      have E := BstLean.Part269.S17.uniformEnergy10 (n := 12791) (by norm_num)
        (q := 1 - (cell12791 ⟨10,by decide⟩).lower)
        (by norm_num [cell12791]) (by norm_num [cell12791])
      exact ⟨E.1,E.2.trans (by norm_num [cell12791])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy11 (n := 12791) (by norm_num)
        (q := 1 - (cell12791 ⟨11,by decide⟩).lower)
        (by norm_num [cell12791]) (by norm_num [cell12791])
      exact ⟨E.1,E.2.trans (by norm_num [cell12791])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy12 (n := 12791) (by norm_num)
        (q := 1 - (cell12791 ⟨12,by decide⟩).lower)
        (by norm_num [cell12791]) (by norm_num [cell12791])
      exact ⟨E.1,E.2.trans (by norm_num [cell12791])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy13 (n := 12791) (by norm_num)
        (q := 1 - (cell12791 ⟨13,by decide⟩).lower)
        (by norm_num [cell12791]) (by norm_num [cell12791])
      exact ⟨E.1,E.2.trans (by norm_num [cell12791])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy14 (n := 12791) (by norm_num)
        (q := 1 - (cell12791 ⟨14,by decide⟩).lower)
        (by norm_num [cell12791]) (by norm_num [cell12791])
      exact ⟨E.1,E.2.trans (by norm_num [cell12791])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy15 (n := 12791) (by norm_num)
        (q := 1 - (cell12791 ⟨15,by decide⟩).lower)
        (by norm_num [cell12791]) (by norm_num [cell12791])
      exact ⟨E.1,E.2.trans (by norm_num [cell12791])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy16 (n := 12791) (by norm_num)
        (q := 1 - (cell12791 ⟨16,by decide⟩).lower)
        (by norm_num [cell12791]) (by norm_num [cell12791])
      exact ⟨E.1,E.2.trans (by norm_num [cell12791])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy17 (n := 12791) (by norm_num)
        (q := 1 - (cell12791 ⟨17,by decide⟩).lower)
        (by norm_num [cell12791]) (by norm_num [cell12791])
      exact ⟨E.1,E.2.trans (by norm_num [cell12791])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy18 (n := 12791) (by norm_num)
        (q := 1 - (cell12791 ⟨18,by decide⟩).lower)
        (by norm_num [cell12791]) (by norm_num [cell12791])
      exact ⟨E.1,E.2.trans (by norm_num [cell12791])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy19 (n := 12791) (by norm_num)
        (q := 1 - (cell12791 ⟨19,by decide⟩).lower)
        (by norm_num [cell12791]) (by norm_num [cell12791])
      exact ⟨E.1,E.2.trans (by norm_num [cell12791])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy20 (n := 12791) (by norm_num)
        (q := 1 - (cell12791 ⟨20,by decide⟩).lower)
        (by norm_num [cell12791]) (by norm_num [cell12791])
      exact ⟨E.1,E.2.trans (by norm_num [cell12791])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy21 (n := 12791) (by norm_num)
        (q := 1 - (cell12791 ⟨21,by decide⟩).lower)
        (by norm_num [cell12791]) (by norm_num [cell12791])
      exact ⟨E.1,E.2.trans (by norm_num [cell12791])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy22 (n := 12791) (by norm_num)
        (q := 1 - (cell12791 ⟨22,by decide⟩).lower)
        (by norm_num [cell12791]) (by norm_num [cell12791])
      exact ⟨E.1,E.2.trans (by norm_num [cell12791])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy23 (n := 12791) (by norm_num)
        (q := 1 - (cell12791 ⟨23,by decide⟩).lower)
        (by norm_num [cell12791]) (by norm_num [cell12791])
      exact ⟨E.1,E.2.trans (by norm_num [cell12791])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy24 (n := 12791) (by norm_num)
        (q := 1 - (cell12791 ⟨24,by decide⟩).lower)
        (by norm_num [cell12791]) (by norm_num [cell12791])
      exact ⟨E.1,E.2.trans (by norm_num [cell12791])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy25 (n := 12791) (by norm_num)
        (q := 1 - (cell12791 ⟨25,by decide⟩).lower)
        (by norm_num [cell12791]) (by norm_num [cell12791])
      exact ⟨E.1,E.2.trans (by norm_num [cell12791])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy26 (n := 12791) (by norm_num)
        (q := 1 - (cell12791 ⟨26,by decide⟩).lower)
        (by norm_num [cell12791]) (by norm_num [cell12791])
      exact ⟨E.1,E.2.trans (by norm_num [cell12791])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy27 (n := 12791) (by norm_num)
        (q := 1 - (cell12791 ⟨27,by decide⟩).lower)
        (by norm_num [cell12791]) (by norm_num [cell12791])
      exact ⟨E.1,E.2.trans (by norm_num [cell12791])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy28 (n := 12791) (by norm_num)
        (q := 1 - (cell12791 ⟨28,by decide⟩).lower)
        (by norm_num [cell12791]) (by norm_num [cell12791])
      exact ⟨E.1,E.2.trans (by norm_num [cell12791])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy29 (n := 12791) (by norm_num)
        (q := 1 - (cell12791 ⟨29,by decide⟩).lower)
        (by norm_num [cell12791]) (by norm_num [cell12791])
      exact ⟨E.1,E.2.trans (by norm_num [cell12791])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy30 (n := 12791) (by norm_num)
        (q := 1 - (cell12791 ⟨30,by decide⟩).lower)
        (by norm_num [cell12791]) (by norm_num [cell12791])
      exact ⟨E.1,E.2.trans (by norm_num [cell12791])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy31 (n := 12791) (by norm_num)
        (q := 1 - (cell12791 ⟨31,by decide⟩).lower)
        (by norm_num [cell12791]) (by norm_num [cell12791])
      exact ⟨E.1,E.2.trans (by norm_num [cell12791])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy32 (n := 12791) (by norm_num)
        (q := 1 - (cell12791 ⟨32,by decide⟩).lower)
        (by norm_num [cell12791]) (by norm_num [cell12791])
      exact ⟨E.1,E.2.trans (by norm_num [cell12791])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy33 (n := 12791) (by norm_num)
        (q := 1 - (cell12791 ⟨33,by decide⟩).lower)
        (by norm_num [cell12791]) (by norm_num [cell12791])
      exact ⟨E.1,E.2.trans (by norm_num [cell12791])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy34 (n := 12791) (by norm_num)
        (q := 1 - (cell12791 ⟨34,by decide⟩).lower)
        (by norm_num [cell12791]) (by norm_num [cell12791])
      exact ⟨E.1,E.2.trans (by norm_num [cell12791])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy35 (n := 12791) (by norm_num)
        (q := 1 - (cell12791 ⟨35,by decide⟩).lower)
        (by norm_num [cell12791]) (by norm_num [cell12791])
      exact ⟨E.1,E.2.trans (by norm_num [cell12791])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy36 (n := 12791) (by norm_num)
        (q := 1 - (cell12791 ⟨36,by decide⟩).lower)
        (by norm_num [cell12791]) (by norm_num [cell12791])
      exact ⟨E.1,E.2.trans (by norm_num [cell12791])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy37 (n := 12791) (by norm_num)
        (q := 1 - (cell12791 ⟨37,by decide⟩).lower)
        (by norm_num [cell12791]) (by norm_num [cell12791])
      exact ⟨E.1,E.2.trans (by norm_num [cell12791])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy38 (n := 12791) (by norm_num)
        (q := 1 - (cell12791 ⟨38,by decide⟩).lower)
        (by norm_num [cell12791]) (by norm_num [cell12791])
      exact ⟨E.1,E.2.trans (by norm_num [cell12791])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy39 (n := 12791) (by norm_num)
        (q := 1 - (cell12791 ⟨39,by decide⟩).lower)
        (by norm_num [cell12791]) (by norm_num [cell12791])
      exact ⟨E.1,E.2.trans (by norm_num [cell12791])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy40 (n := 12791) (by norm_num)
        (q := 1 - (cell12791 ⟨40,by decide⟩).lower)
        (by norm_num [cell12791]) (by norm_num [cell12791])
      exact ⟨E.1,E.2.trans (by norm_num [cell12791])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy41 (n := 12791) (by norm_num)
        (q := 1 - (cell12791 ⟨41,by decide⟩).lower)
        (by norm_num [cell12791]) (by norm_num [cell12791])
      exact ⟨E.1,E.2.trans (by norm_num [cell12791])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy42 (n := 12791) (by norm_num)
        (q := 1 - (cell12791 ⟨42,by decide⟩).lower)
        (by norm_num [cell12791]) (by norm_num [cell12791])
      exact ⟨E.1,E.2.trans (by norm_num [cell12791])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy43 (n := 12791) (by norm_num)
        (q := 1 - (cell12791 ⟨43,by decide⟩).lower)
        (by norm_num [cell12791]) (by norm_num [cell12791])
      exact ⟨E.1,E.2.trans (by norm_num [cell12791])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy44 (n := 12791) (by norm_num)
        (q := 1 - (cell12791 ⟨44,by decide⟩).lower)
        (by norm_num [cell12791]) (by norm_num [cell12791])
      exact ⟨E.1,E.2.trans (by norm_num [cell12791])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy45 (n := 12791) (by norm_num)
        (q := 1 - (cell12791 ⟨45,by decide⟩).lower)
        (by norm_num [cell12791]) (by norm_num [cell12791])
      exact ⟨E.1,E.2.trans (by norm_num [cell12791])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy46 (n := 12791) (by norm_num)
        (q := 1 - (cell12791 ⟨46,by decide⟩).lower)
        (by norm_num [cell12791]) (by norm_num [cell12791])
      exact ⟨E.1,E.2.trans (by norm_num [cell12791])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy47 (n := 12791) (by norm_num)
        (q := 1 - (cell12791 ⟨47,by decide⟩).lower)
        (by norm_num [cell12791]) (by norm_num [cell12791])
      exact ⟨E.1,E.2.trans (by norm_num [cell12791])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy48 (n := 12791) (by norm_num)
        (q := 1 - (cell12791 ⟨48,by decide⟩).lower)
        (by norm_num [cell12791]) (by norm_num [cell12791])
      exact ⟨E.1,E.2.trans (by norm_num [cell12791])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy49 (n := 12791) (by norm_num)
        (q := 1 - (cell12791 ⟨49,by decide⟩).lower)
        (by norm_num [cell12791]) (by norm_num [cell12791])
      exact ⟨E.1,E.2.trans (by norm_num [cell12791])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy50 (n := 12791) (by norm_num)
        (q := 1 - (cell12791 ⟨50,by decide⟩).lower)
        (by norm_num [cell12791]) (by norm_num [cell12791])
      exact ⟨E.1,E.2.trans (by norm_num [cell12791])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy51 (n := 12791) (by norm_num)
        (q := 1 - (cell12791 ⟨51,by decide⟩).lower)
        (by norm_num [cell12791]) (by norm_num [cell12791])
      exact ⟨E.1,E.2.trans (by norm_num [cell12791])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy52 (n := 12791) (by norm_num)
        (q := 1 - (cell12791 ⟨52,by decide⟩).lower)
        (by norm_num [cell12791]) (by norm_num [cell12791])
      exact ⟨E.1,E.2.trans (by norm_num [cell12791])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12791

/-! Source-cell containment and simple scalar guards at 12791. -/
namespace BstLean.Part269.N12791
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12791)
open BstLean.Part268 (cell12791)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12791 ⟨10,by decide⟩).lower ∧ (cell12791 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12791 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12791 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12791 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12791 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12791 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12791,cell12791,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12791 ⟨11,by decide⟩).lower ∧ (cell12791 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12791 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12791 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12791 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12791 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12791 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12791,cell12791,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12791 ⟨12,by decide⟩).lower ∧ (cell12791 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12791 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12791 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12791 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12791 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12791 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12791,cell12791,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12791 ⟨13,by decide⟩).lower ∧ (cell12791 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12791 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12791 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12791 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12791 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12791 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12791,cell12791,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12791 ⟨14,by decide⟩).lower ∧ (cell12791 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12791 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12791 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12791 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12791 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12791 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12791,cell12791,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12791 ⟨15,by decide⟩).lower ∧ (cell12791 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12791 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12791 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12791 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12791 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12791 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12791,cell12791,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12791 ⟨16,by decide⟩).lower ∧ (cell12791 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12791 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12791 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12791 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12791 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12791 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12791,cell12791,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12791 ⟨17,by decide⟩).lower ∧ (cell12791 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12791 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12791 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12791 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12791 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12791 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12791,cell12791,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12791 ⟨18,by decide⟩).lower ∧ (cell12791 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12791 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12791 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12791 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12791 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12791 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12791,cell12791,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12791 ⟨19,by decide⟩).lower ∧ (cell12791 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12791 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12791 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12791 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12791 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12791 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12791,cell12791,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12791 ⟨20,by decide⟩).lower ∧ (cell12791 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12791 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12791 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12791 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12791 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12791 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12791,cell12791,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12791 ⟨21,by decide⟩).lower ∧ (cell12791 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12791 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12791 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12791 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12791 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12791 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12791,cell12791,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12791 ⟨22,by decide⟩).lower ∧ (cell12791 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12791 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12791 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12791 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12791 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12791 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12791,cell12791,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12791 ⟨23,by decide⟩).lower ∧ (cell12791 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12791 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12791 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12791 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12791 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12791 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12791,cell12791,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12791 ⟨24,by decide⟩).lower ∧ (cell12791 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12791 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12791 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12791 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12791 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12791 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12791,cell12791,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12791 ⟨25,by decide⟩).lower ∧ (cell12791 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12791 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12791 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12791 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12791 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12791 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12791,cell12791,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12791 ⟨26,by decide⟩).lower ∧ (cell12791 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12791 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12791 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12791 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12791 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12791 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12791,cell12791,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12791 ⟨27,by decide⟩).lower ∧ (cell12791 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12791 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12791 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12791 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12791 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12791 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12791,cell12791,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12791 ⟨28,by decide⟩).lower ∧ (cell12791 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12791 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12791 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12791 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12791 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12791 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12791,cell12791,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12791 ⟨29,by decide⟩).lower ∧ (cell12791 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12791 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12791 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12791 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12791 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12791 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12791,cell12791,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12791 ⟨30,by decide⟩).lower ∧ (cell12791 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12791 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12791 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12791 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12791 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12791 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12791,cell12791,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12791 ⟨31,by decide⟩).lower ∧ (cell12791 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12791 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12791 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12791 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12791 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12791 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12791,cell12791,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12791 ⟨32,by decide⟩).lower ∧ (cell12791 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12791 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12791 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12791 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12791 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12791 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12791,cell12791,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12791 ⟨33,by decide⟩).lower ∧ (cell12791 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12791 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12791 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12791 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12791 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12791 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12791,cell12791,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12791 ⟨34,by decide⟩).lower ∧ (cell12791 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12791 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12791 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12791 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12791 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12791 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12791,cell12791,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12791 ⟨35,by decide⟩).lower ∧ (cell12791 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12791 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12791 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12791 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12791 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12791 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12791,cell12791,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12791 ⟨36,by decide⟩).lower ∧ (cell12791 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12791 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12791 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12791 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12791 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12791 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12791,cell12791,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12791 ⟨37,by decide⟩).lower ∧ (cell12791 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12791 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12791 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12791 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12791 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12791 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12791,cell12791,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12791 ⟨38,by decide⟩).lower ∧ (cell12791 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12791 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12791 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12791 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12791 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12791 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12791,cell12791,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12791 ⟨39,by decide⟩).lower ∧ (cell12791 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12791 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12791 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12791 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12791 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12791 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12791,cell12791,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12791 ⟨40,by decide⟩).lower ∧ (cell12791 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12791 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12791 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12791 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12791 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12791 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12791,cell12791,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12791 ⟨41,by decide⟩).lower ∧ (cell12791 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12791 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12791 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12791 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12791 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12791 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12791,cell12791,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12791 ⟨42,by decide⟩).lower ∧ (cell12791 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12791 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12791 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12791 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12791 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12791 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12791,cell12791,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12791 ⟨43,by decide⟩).lower ∧ (cell12791 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12791 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12791 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12791 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12791 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12791 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12791,cell12791,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12791 ⟨44,by decide⟩).lower ∧ (cell12791 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12791 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12791 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12791 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12791 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12791 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12791,cell12791,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12791 ⟨45,by decide⟩).lower ∧ (cell12791 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12791 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12791 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12791 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12791 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12791 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12791,cell12791,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12791 ⟨46,by decide⟩).lower ∧ (cell12791 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12791 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12791 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12791 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12791 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12791 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12791,cell12791,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12791 ⟨47,by decide⟩).lower ∧ (cell12791 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12791 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12791 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12791 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12791 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12791 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12791,cell12791,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12791 ⟨48,by decide⟩).lower ∧ (cell12791 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12791 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12791 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12791 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12791 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12791 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12791,cell12791,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12791 ⟨49,by decide⟩).lower ∧ (cell12791 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12791 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12791 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12791 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12791 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12791 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12791,cell12791,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12791 ⟨50,by decide⟩).lower ∧ (cell12791 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12791 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12791 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12791 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12791 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12791 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12791,cell12791,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12791 ⟨51,by decide⟩).lower ∧ (cell12791 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12791 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12791 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12791 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12791 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12791 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12791,cell12791,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12791 ⟨52,by decide⟩).lower ∧ (cell12791 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12791 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12791 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12791 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12791 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12791 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12791,cell12791,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12791 i).lower ∧
    (cell12791 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12791 i).upper ≤ (0.532 : ℝ) ∧
    (cell12791 i).centre ≤ (0.1 : ℝ) ∧ (cell12791 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12791 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12791 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12791

/-! The local source numeric instances at 12791 have no network premises. -/
namespace BstLean.Part269.N12791
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12791)
open BstLean.Part268 (cell12791)

noncomputable def sourceNumerics12791 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12791 (cell12791 i)
      scalarRow12791.M scalarRow12791.H scalarRow12791.xi := by
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
    energy_allowance := scalarRow12791.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12791]
    centre_nonneg := (scalarRow12791.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D17.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12791])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12791
/-! Actual 12792 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12792
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12792 ≤ (1.035679088220 : ℝ) := by
  have hr : (113.101724124789 : ℝ) ≤ √(12792 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.101724124789 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12792 12792 (11 / 1000) ≤
    (0.008451568799 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12792) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.101724124789 : ℝ) ≤ √(12792 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12792)
  have hdiv : K / √(12792 : ℝ) ≤ K / 113.101724124789 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.101724124789 ≤ (0.008451568799 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12792.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12792 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12792 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12792 := gPlus_lower 12792
end BstLean.Part269.N12792

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12792
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035679088219 : ℝ) ≤ wn 12792 := by
  have hn : √(12792 : ℝ) ≤ 113.101724124790 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12792 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.101724124790 ≤ 2 / √(12792 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000250037926 : ℝ) ≤ rhoBar 12792 BstLean.Part154.csC ∧
    rhoBar 12792 BstLean.Part154.csC ≤ 0.000250038313 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035679088219 : ℝ) / (1.295212 * 12792) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035679088220 : ℝ) / (1.29521 * 12792) := by gcongr
      _ ≤ (0.000250038313 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12792 BstLean.Part154.csC) ≤ 0.001000215772 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12792 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12792 BstLean.Part154.csC) (piBar (rhoBar 12792 BstLean.Part154.csC)) ≤ 0.000190980885 ∧
    cc1 (rhoBar 12792 BstLean.Part154.csC) (piBar (rhoBar 12792 BstLean.Part154.csC)) ≤ 0.000121522419 ∧
    cc2 (rhoBar 12792 BstLean.Part154.csC) ≤ 0.000070544711 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12792 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12792 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12792 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12792 BstLean.Part154.csC * nuR (rhoBar 12792 BstLean.Part154.csC)) ≤ 0.000500092256 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000250038313 : ℝ) * 0.001000215772 := by gcongr
      _ ≤ (0.000500092256 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12792 BstLean.Part154.csC) * nuR (rhoBar 12792 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001000215772 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12792 BstLean.Part154.csC) * rhoBar 12792 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000250038313 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000250038313 / 2 + 0.399 * 0.001000215772 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000190980885 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000500092256 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121522419 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000250038313 / 1.414213562 := by gcongr
      _ ≤ (0.000070544711 : ℝ) := by norm_num

end BstLean.Part269.N12792

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12792
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12792 BstLean.Part154.csC) (piBar (rhoBar 12792 BstLean.Part154.csC)) ≤ 1.57513E-7 := by
  have hr0 : 0 ≤ rhoBar 12792 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12792 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12792 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12792 BstLean.Part154.csC) (piBar (rhoBar 12792 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12792 BstLean.Part154.csC) (piBar (rhoBar 12792 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12792 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000190980885 : ℝ) ^ 2 + 0.000121522419 ^ 2 + 3 * 0.000070544711 ^ 2 +
        2 * 0.797885 * 0.000190980885 * 0.000121522419 + 2 * 0.000190980885 * 0.000070544711 +
        4 * 0.797885 * 0.000121522419 * 0.000070544711 := by gcongr
    _ ≤ (1.57513E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12792 BstLean.Part154.csC Θ ≤ 0.002609730817 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12792 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12792 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12792 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12792 BstLean.Part154.csC) (piBar (rhoBar 12792 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12792 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035679088220 * 1.57513E-7 / (0.000250037926 : ℝ) := by gcongr
    _ ≤ 0.002609730817 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12792 BstLean.Part154.csC Θ ≤ 0.002895263695 + 0.000659434967 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12792 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12792 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12792 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035679088220 : ℝ) * ((2 * Θ * 0.000250038313 +
        (6863 / 10000) * 0.000250038313 * 12792 * 0.001000215772) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002895263695 + 0.000659434967 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12792 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12792 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12792 0.011 Θ ∧ gammaRatio 12792 0.011 Θ ≤ 0.000085956706 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12792 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035679088220 : ℝ) * 0.525 / ((1 - 0.011) * 12792) := by gcongr
      _ ≤ (0.000085956706 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12792 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12792 0.011 Θ) :=
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
    badAllowance 12792 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000560204559 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12792 BstLean.Part154.csC) 1.22 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 2 (rhoBar 12792 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12792 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12792 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12792 0.011 Θ) 1.12 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 1 (gammaRatio 12792 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12792 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12792 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12792 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12792 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035679088220 : ℝ) * 12792 *
        (1.8602E-8 / 1.1045361 + 2.2721E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000560204559 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12792 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003455468254 + 0.003269165784 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12792

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12792
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12792 BstLean.Part154.csC) (piBar (rhoBar 12792 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12792 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12792 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12792 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12792 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12792 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12792 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12792 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12792 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12792 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12792 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12792 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12792 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12792 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12792 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052293195940 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12792) ≤ 0.010558968843 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12792 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035679088220)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010558968843 + 2 * 0.737676 / 12792) := by gcongr
    _ ≤ (0.052293195940 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12792 12 ≤ 0.0015 := by
  exact BstLean.Part269.S17.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12792

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12792
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560507698882 : ℝ) ≤ plow 12792 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12792) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052678380291)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001370108679) : eMP 12792 0.011 xi bn ≤ 0.001179662725 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12792 : ℝ) * (1 - 0.011))) ≤ 0.000583290762 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001370108679 / (12792 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000583290762 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000583290762 : ℝ) + 3.141593 * 0.052678380291 / (12792 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001179662725 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052678380291)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001370108679) : PiBarMP 12792 12 0.011 xi bn ≤ 0.160664478333 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12792 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037014979117 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.477944504689 : ℝ) ≤ √((12792 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.101724124789 : ℝ) ≤ √(12792 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12792) ≤ 0.123184755764 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037014979117 + 0.052678380291 * 1.772454 / (2 * (112.477944504689 : ℝ))) * (1 + 0.001179662725) +
        8 / (12792 * 113.101724124789) + 0.123184755764 := by gcongr
    _ ≤ (0.160664478333 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052678380291)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001370108679) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281810908309) :
    parallelOracle 12792 0.011 xi bn cd ≤ 0.161647959650 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12792 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12792 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560507698882 : ℝ) ≤ plow 12792 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.101724124789 : ℝ) ≤ √(12792 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281810908309 : ℝ) / (2 * 0.560507698882 * 113.101724124789)) * 0.160664478333 +
        0.281810908309 ^ 2 / (2 * 0.560507698882 * 113.101724124789) := by gcongr
    _ ≤ (0.161647959650 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052678380291) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001370108679)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281810908309) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12792 12792 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560507698882 : ℝ) ≤ plow 12792 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.101724124789 : ℝ) ≤ √(12792 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12792 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12792 Θ 1.22 ≤ 0.011724847789 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.101724124789 := by gcongr <;> linarith
      _ ≤ (0.011724847789 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12792 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12792 12792 0.011 ≤ 0.008451568799 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12792 12792 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12792 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12792 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12792 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12792 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161647959650 + 0.011724847789 + (0.008451568799 : ℝ) *
        (1 + 2 * (0.281810908309 + 0.011724847789) / (0.560507698882 * 113.101724124789))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12792]

end BstLean.Part269.N12792

/-! The original eight local profiles supply actual 12792 moment certificates. -/
namespace BstLean.Part269.N12792
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12792 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12792 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12792 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052678380291 ∧
    0 ≤ bN 12792 BstLean.Part154.csC (groupTheta g) ∧ bN 12792 BstLean.Part154.csC (groupTheta g) ≤ 0.001370108679 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12792 12792 0.011
      (momentAllowance 12792 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12792 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12792 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12792 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12792 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12792 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229517712369 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12792 0.011
      (momentAllowance 12792 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12792 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12792
/-! The actual computed-centre upper energy formula at 12792. -/
namespace BstLean.Part269.N12792
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12792

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12792
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12792)
open BstLean.Part268 (cell12792)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085226405995
  | 2 => 0.086164407051
  | 3 => 0.087099871207
  | 4 => 0.088034059560
  | 5 => 0.088968502463
  | 6 => 0.089905040167
  | 7 => 0.090845867391
  | 8 => 0.091793581903
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12792 12792 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12792 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003459522332 + 0.003273654356 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S17.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12792

/-! Actual upper energy certificates on all 43 source endpoints at 12792. -/
namespace BstLean.Part269.N12792
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12792)
open BstLean.Part268 (cell12792)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12792 (gMinus 12792) (1 - (cell12792 i).lower) ≤ 1 ∧
    energyUpper 12792 (gMinus 12792) (BstLean.Part211.gPlus 12792)
      (finiteEnergy 12792 12792 0.011) (1 - (cell12792 i).lower) ≤
      (cell12792 i).energy := by
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
      have E := BstLean.Part269.S17.uniformEnergy10 (n := 12792) (by norm_num)
        (q := 1 - (cell12792 ⟨10,by decide⟩).lower)
        (by norm_num [cell12792]) (by norm_num [cell12792])
      exact ⟨E.1,E.2.trans (by norm_num [cell12792])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy11 (n := 12792) (by norm_num)
        (q := 1 - (cell12792 ⟨11,by decide⟩).lower)
        (by norm_num [cell12792]) (by norm_num [cell12792])
      exact ⟨E.1,E.2.trans (by norm_num [cell12792])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy12 (n := 12792) (by norm_num)
        (q := 1 - (cell12792 ⟨12,by decide⟩).lower)
        (by norm_num [cell12792]) (by norm_num [cell12792])
      exact ⟨E.1,E.2.trans (by norm_num [cell12792])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy13 (n := 12792) (by norm_num)
        (q := 1 - (cell12792 ⟨13,by decide⟩).lower)
        (by norm_num [cell12792]) (by norm_num [cell12792])
      exact ⟨E.1,E.2.trans (by norm_num [cell12792])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy14 (n := 12792) (by norm_num)
        (q := 1 - (cell12792 ⟨14,by decide⟩).lower)
        (by norm_num [cell12792]) (by norm_num [cell12792])
      exact ⟨E.1,E.2.trans (by norm_num [cell12792])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy15 (n := 12792) (by norm_num)
        (q := 1 - (cell12792 ⟨15,by decide⟩).lower)
        (by norm_num [cell12792]) (by norm_num [cell12792])
      exact ⟨E.1,E.2.trans (by norm_num [cell12792])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy16 (n := 12792) (by norm_num)
        (q := 1 - (cell12792 ⟨16,by decide⟩).lower)
        (by norm_num [cell12792]) (by norm_num [cell12792])
      exact ⟨E.1,E.2.trans (by norm_num [cell12792])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy17 (n := 12792) (by norm_num)
        (q := 1 - (cell12792 ⟨17,by decide⟩).lower)
        (by norm_num [cell12792]) (by norm_num [cell12792])
      exact ⟨E.1,E.2.trans (by norm_num [cell12792])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy18 (n := 12792) (by norm_num)
        (q := 1 - (cell12792 ⟨18,by decide⟩).lower)
        (by norm_num [cell12792]) (by norm_num [cell12792])
      exact ⟨E.1,E.2.trans (by norm_num [cell12792])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy19 (n := 12792) (by norm_num)
        (q := 1 - (cell12792 ⟨19,by decide⟩).lower)
        (by norm_num [cell12792]) (by norm_num [cell12792])
      exact ⟨E.1,E.2.trans (by norm_num [cell12792])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy20 (n := 12792) (by norm_num)
        (q := 1 - (cell12792 ⟨20,by decide⟩).lower)
        (by norm_num [cell12792]) (by norm_num [cell12792])
      exact ⟨E.1,E.2.trans (by norm_num [cell12792])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy21 (n := 12792) (by norm_num)
        (q := 1 - (cell12792 ⟨21,by decide⟩).lower)
        (by norm_num [cell12792]) (by norm_num [cell12792])
      exact ⟨E.1,E.2.trans (by norm_num [cell12792])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy22 (n := 12792) (by norm_num)
        (q := 1 - (cell12792 ⟨22,by decide⟩).lower)
        (by norm_num [cell12792]) (by norm_num [cell12792])
      exact ⟨E.1,E.2.trans (by norm_num [cell12792])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy23 (n := 12792) (by norm_num)
        (q := 1 - (cell12792 ⟨23,by decide⟩).lower)
        (by norm_num [cell12792]) (by norm_num [cell12792])
      exact ⟨E.1,E.2.trans (by norm_num [cell12792])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy24 (n := 12792) (by norm_num)
        (q := 1 - (cell12792 ⟨24,by decide⟩).lower)
        (by norm_num [cell12792]) (by norm_num [cell12792])
      exact ⟨E.1,E.2.trans (by norm_num [cell12792])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy25 (n := 12792) (by norm_num)
        (q := 1 - (cell12792 ⟨25,by decide⟩).lower)
        (by norm_num [cell12792]) (by norm_num [cell12792])
      exact ⟨E.1,E.2.trans (by norm_num [cell12792])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy26 (n := 12792) (by norm_num)
        (q := 1 - (cell12792 ⟨26,by decide⟩).lower)
        (by norm_num [cell12792]) (by norm_num [cell12792])
      exact ⟨E.1,E.2.trans (by norm_num [cell12792])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy27 (n := 12792) (by norm_num)
        (q := 1 - (cell12792 ⟨27,by decide⟩).lower)
        (by norm_num [cell12792]) (by norm_num [cell12792])
      exact ⟨E.1,E.2.trans (by norm_num [cell12792])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy28 (n := 12792) (by norm_num)
        (q := 1 - (cell12792 ⟨28,by decide⟩).lower)
        (by norm_num [cell12792]) (by norm_num [cell12792])
      exact ⟨E.1,E.2.trans (by norm_num [cell12792])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy29 (n := 12792) (by norm_num)
        (q := 1 - (cell12792 ⟨29,by decide⟩).lower)
        (by norm_num [cell12792]) (by norm_num [cell12792])
      exact ⟨E.1,E.2.trans (by norm_num [cell12792])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy30 (n := 12792) (by norm_num)
        (q := 1 - (cell12792 ⟨30,by decide⟩).lower)
        (by norm_num [cell12792]) (by norm_num [cell12792])
      exact ⟨E.1,E.2.trans (by norm_num [cell12792])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy31 (n := 12792) (by norm_num)
        (q := 1 - (cell12792 ⟨31,by decide⟩).lower)
        (by norm_num [cell12792]) (by norm_num [cell12792])
      exact ⟨E.1,E.2.trans (by norm_num [cell12792])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy32 (n := 12792) (by norm_num)
        (q := 1 - (cell12792 ⟨32,by decide⟩).lower)
        (by norm_num [cell12792]) (by norm_num [cell12792])
      exact ⟨E.1,E.2.trans (by norm_num [cell12792])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy33 (n := 12792) (by norm_num)
        (q := 1 - (cell12792 ⟨33,by decide⟩).lower)
        (by norm_num [cell12792]) (by norm_num [cell12792])
      exact ⟨E.1,E.2.trans (by norm_num [cell12792])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy34 (n := 12792) (by norm_num)
        (q := 1 - (cell12792 ⟨34,by decide⟩).lower)
        (by norm_num [cell12792]) (by norm_num [cell12792])
      exact ⟨E.1,E.2.trans (by norm_num [cell12792])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy35 (n := 12792) (by norm_num)
        (q := 1 - (cell12792 ⟨35,by decide⟩).lower)
        (by norm_num [cell12792]) (by norm_num [cell12792])
      exact ⟨E.1,E.2.trans (by norm_num [cell12792])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy36 (n := 12792) (by norm_num)
        (q := 1 - (cell12792 ⟨36,by decide⟩).lower)
        (by norm_num [cell12792]) (by norm_num [cell12792])
      exact ⟨E.1,E.2.trans (by norm_num [cell12792])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy37 (n := 12792) (by norm_num)
        (q := 1 - (cell12792 ⟨37,by decide⟩).lower)
        (by norm_num [cell12792]) (by norm_num [cell12792])
      exact ⟨E.1,E.2.trans (by norm_num [cell12792])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy38 (n := 12792) (by norm_num)
        (q := 1 - (cell12792 ⟨38,by decide⟩).lower)
        (by norm_num [cell12792]) (by norm_num [cell12792])
      exact ⟨E.1,E.2.trans (by norm_num [cell12792])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy39 (n := 12792) (by norm_num)
        (q := 1 - (cell12792 ⟨39,by decide⟩).lower)
        (by norm_num [cell12792]) (by norm_num [cell12792])
      exact ⟨E.1,E.2.trans (by norm_num [cell12792])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy40 (n := 12792) (by norm_num)
        (q := 1 - (cell12792 ⟨40,by decide⟩).lower)
        (by norm_num [cell12792]) (by norm_num [cell12792])
      exact ⟨E.1,E.2.trans (by norm_num [cell12792])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy41 (n := 12792) (by norm_num)
        (q := 1 - (cell12792 ⟨41,by decide⟩).lower)
        (by norm_num [cell12792]) (by norm_num [cell12792])
      exact ⟨E.1,E.2.trans (by norm_num [cell12792])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy42 (n := 12792) (by norm_num)
        (q := 1 - (cell12792 ⟨42,by decide⟩).lower)
        (by norm_num [cell12792]) (by norm_num [cell12792])
      exact ⟨E.1,E.2.trans (by norm_num [cell12792])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy43 (n := 12792) (by norm_num)
        (q := 1 - (cell12792 ⟨43,by decide⟩).lower)
        (by norm_num [cell12792]) (by norm_num [cell12792])
      exact ⟨E.1,E.2.trans (by norm_num [cell12792])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy44 (n := 12792) (by norm_num)
        (q := 1 - (cell12792 ⟨44,by decide⟩).lower)
        (by norm_num [cell12792]) (by norm_num [cell12792])
      exact ⟨E.1,E.2.trans (by norm_num [cell12792])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy45 (n := 12792) (by norm_num)
        (q := 1 - (cell12792 ⟨45,by decide⟩).lower)
        (by norm_num [cell12792]) (by norm_num [cell12792])
      exact ⟨E.1,E.2.trans (by norm_num [cell12792])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy46 (n := 12792) (by norm_num)
        (q := 1 - (cell12792 ⟨46,by decide⟩).lower)
        (by norm_num [cell12792]) (by norm_num [cell12792])
      exact ⟨E.1,E.2.trans (by norm_num [cell12792])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy47 (n := 12792) (by norm_num)
        (q := 1 - (cell12792 ⟨47,by decide⟩).lower)
        (by norm_num [cell12792]) (by norm_num [cell12792])
      exact ⟨E.1,E.2.trans (by norm_num [cell12792])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy48 (n := 12792) (by norm_num)
        (q := 1 - (cell12792 ⟨48,by decide⟩).lower)
        (by norm_num [cell12792]) (by norm_num [cell12792])
      exact ⟨E.1,E.2.trans (by norm_num [cell12792])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy49 (n := 12792) (by norm_num)
        (q := 1 - (cell12792 ⟨49,by decide⟩).lower)
        (by norm_num [cell12792]) (by norm_num [cell12792])
      exact ⟨E.1,E.2.trans (by norm_num [cell12792])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy50 (n := 12792) (by norm_num)
        (q := 1 - (cell12792 ⟨50,by decide⟩).lower)
        (by norm_num [cell12792]) (by norm_num [cell12792])
      exact ⟨E.1,E.2.trans (by norm_num [cell12792])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy51 (n := 12792) (by norm_num)
        (q := 1 - (cell12792 ⟨51,by decide⟩).lower)
        (by norm_num [cell12792]) (by norm_num [cell12792])
      exact ⟨E.1,E.2.trans (by norm_num [cell12792])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy52 (n := 12792) (by norm_num)
        (q := 1 - (cell12792 ⟨52,by decide⟩).lower)
        (by norm_num [cell12792]) (by norm_num [cell12792])
      exact ⟨E.1,E.2.trans (by norm_num [cell12792])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12792

/-! Source-cell containment and simple scalar guards at 12792. -/
namespace BstLean.Part269.N12792
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12792)
open BstLean.Part268 (cell12792)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12792 ⟨10,by decide⟩).lower ∧ (cell12792 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12792 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12792 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12792 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12792 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12792 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12792,cell12792,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12792 ⟨11,by decide⟩).lower ∧ (cell12792 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12792 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12792 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12792 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12792 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12792 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12792,cell12792,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12792 ⟨12,by decide⟩).lower ∧ (cell12792 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12792 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12792 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12792 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12792 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12792 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12792,cell12792,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12792 ⟨13,by decide⟩).lower ∧ (cell12792 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12792 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12792 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12792 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12792 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12792 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12792,cell12792,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12792 ⟨14,by decide⟩).lower ∧ (cell12792 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12792 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12792 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12792 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12792 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12792 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12792,cell12792,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12792 ⟨15,by decide⟩).lower ∧ (cell12792 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12792 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12792 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12792 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12792 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12792 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12792,cell12792,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12792 ⟨16,by decide⟩).lower ∧ (cell12792 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12792 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12792 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12792 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12792 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12792 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12792,cell12792,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12792 ⟨17,by decide⟩).lower ∧ (cell12792 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12792 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12792 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12792 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12792 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12792 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12792,cell12792,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12792 ⟨18,by decide⟩).lower ∧ (cell12792 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12792 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12792 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12792 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12792 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12792 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12792,cell12792,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12792 ⟨19,by decide⟩).lower ∧ (cell12792 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12792 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12792 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12792 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12792 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12792 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12792,cell12792,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12792 ⟨20,by decide⟩).lower ∧ (cell12792 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12792 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12792 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12792 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12792 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12792 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12792,cell12792,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12792 ⟨21,by decide⟩).lower ∧ (cell12792 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12792 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12792 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12792 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12792 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12792 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12792,cell12792,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12792 ⟨22,by decide⟩).lower ∧ (cell12792 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12792 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12792 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12792 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12792 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12792 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12792,cell12792,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12792 ⟨23,by decide⟩).lower ∧ (cell12792 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12792 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12792 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12792 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12792 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12792 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12792,cell12792,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12792 ⟨24,by decide⟩).lower ∧ (cell12792 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12792 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12792 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12792 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12792 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12792 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12792,cell12792,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12792 ⟨25,by decide⟩).lower ∧ (cell12792 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12792 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12792 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12792 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12792 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12792 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12792,cell12792,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12792 ⟨26,by decide⟩).lower ∧ (cell12792 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12792 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12792 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12792 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12792 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12792 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12792,cell12792,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12792 ⟨27,by decide⟩).lower ∧ (cell12792 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12792 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12792 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12792 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12792 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12792 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12792,cell12792,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12792 ⟨28,by decide⟩).lower ∧ (cell12792 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12792 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12792 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12792 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12792 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12792 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12792,cell12792,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12792 ⟨29,by decide⟩).lower ∧ (cell12792 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12792 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12792 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12792 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12792 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12792 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12792,cell12792,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12792 ⟨30,by decide⟩).lower ∧ (cell12792 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12792 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12792 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12792 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12792 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12792 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12792,cell12792,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12792 ⟨31,by decide⟩).lower ∧ (cell12792 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12792 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12792 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12792 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12792 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12792 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12792,cell12792,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12792 ⟨32,by decide⟩).lower ∧ (cell12792 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12792 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12792 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12792 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12792 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12792 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12792,cell12792,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12792 ⟨33,by decide⟩).lower ∧ (cell12792 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12792 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12792 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12792 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12792 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12792 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12792,cell12792,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12792 ⟨34,by decide⟩).lower ∧ (cell12792 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12792 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12792 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12792 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12792 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12792 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12792,cell12792,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12792 ⟨35,by decide⟩).lower ∧ (cell12792 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12792 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12792 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12792 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12792 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12792 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12792,cell12792,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12792 ⟨36,by decide⟩).lower ∧ (cell12792 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12792 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12792 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12792 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12792 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12792 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12792,cell12792,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12792 ⟨37,by decide⟩).lower ∧ (cell12792 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12792 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12792 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12792 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12792 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12792 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12792,cell12792,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12792 ⟨38,by decide⟩).lower ∧ (cell12792 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12792 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12792 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12792 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12792 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12792 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12792,cell12792,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12792 ⟨39,by decide⟩).lower ∧ (cell12792 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12792 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12792 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12792 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12792 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12792 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12792,cell12792,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12792 ⟨40,by decide⟩).lower ∧ (cell12792 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12792 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12792 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12792 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12792 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12792 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12792,cell12792,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12792 ⟨41,by decide⟩).lower ∧ (cell12792 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12792 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12792 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12792 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12792 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12792 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12792,cell12792,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12792 ⟨42,by decide⟩).lower ∧ (cell12792 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12792 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12792 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12792 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12792 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12792 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12792,cell12792,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12792 ⟨43,by decide⟩).lower ∧ (cell12792 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12792 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12792 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12792 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12792 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12792 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12792,cell12792,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12792 ⟨44,by decide⟩).lower ∧ (cell12792 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12792 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12792 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12792 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12792 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12792 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12792,cell12792,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12792 ⟨45,by decide⟩).lower ∧ (cell12792 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12792 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12792 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12792 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12792 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12792 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12792,cell12792,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12792 ⟨46,by decide⟩).lower ∧ (cell12792 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12792 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12792 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12792 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12792 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12792 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12792,cell12792,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12792 ⟨47,by decide⟩).lower ∧ (cell12792 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12792 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12792 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12792 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12792 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12792 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12792,cell12792,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12792 ⟨48,by decide⟩).lower ∧ (cell12792 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12792 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12792 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12792 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12792 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12792 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12792,cell12792,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12792 ⟨49,by decide⟩).lower ∧ (cell12792 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12792 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12792 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12792 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12792 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12792 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12792,cell12792,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12792 ⟨50,by decide⟩).lower ∧ (cell12792 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12792 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12792 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12792 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12792 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12792 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12792,cell12792,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12792 ⟨51,by decide⟩).lower ∧ (cell12792 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12792 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12792 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12792 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12792 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12792 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12792,cell12792,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12792 ⟨52,by decide⟩).lower ∧ (cell12792 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12792 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12792 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12792 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12792 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12792 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12792,cell12792,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12792 i).lower ∧
    (cell12792 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12792 i).upper ≤ (0.532 : ℝ) ∧
    (cell12792 i).centre ≤ (0.1 : ℝ) ∧ (cell12792 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12792 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12792 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12792

/-! The local source numeric instances at 12792 have no network premises. -/
namespace BstLean.Part269.N12792
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12792)
open BstLean.Part268 (cell12792)

noncomputable def sourceNumerics12792 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12792 (cell12792 i)
      scalarRow12792.M scalarRow12792.H scalarRow12792.xi := by
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
    energy_allowance := scalarRow12792.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12792]
    centre_nonneg := (scalarRow12792.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D17.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12792])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12792
/-! Actual 12793 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12793
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12793 ≤ (1.035677681494 : ℝ) := by
  have hr : (113.106144837493 : ℝ) ≤ √(12793 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.106144837493 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12793 12793 (11 / 1000) ≤
    (0.008451238470 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12793) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.106144837493 : ℝ) ≤ √(12793 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12793)
  have hdiv : K / √(12793 : ℝ) ≤ K / 113.106144837493 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.106144837493 ≤ (0.008451238470 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12793.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12793 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12793 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12793 := gPlus_lower 12793
end BstLean.Part269.N12793

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12793
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035677681493 : ℝ) ≤ wn 12793 := by
  have hn : √(12793 : ℝ) ≤ 113.106144837494 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12793 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.106144837494 ≤ 2 / √(12793 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000250018041 : ℝ) ≤ rhoBar 12793 BstLean.Part154.csC ∧
    rhoBar 12793 BstLean.Part154.csC ≤ 0.000250018428 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035677681493 : ℝ) / (1.295212 * 12793) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035677681494 : ℝ) / (1.29521 * 12793) := by gcongr
      _ ≤ (0.000250018428 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12793 BstLean.Part154.csC) ≤ 0.001000136222 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12793 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12793 BstLean.Part154.csC) (piBar (rhoBar 12793 BstLean.Part154.csC)) ≤ 0.000190965696 ∧
    cc1 (rhoBar 12793 BstLean.Part154.csC) (piBar (rhoBar 12793 BstLean.Part154.csC)) ≤ 0.000121512754 ∧
    cc2 (rhoBar 12793 BstLean.Part154.csC) ≤ 0.000070539101 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12793 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12793 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12793 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12793 BstLean.Part154.csC * nuR (rhoBar 12793 BstLean.Part154.csC)) ≤ 0.000500052484 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000250018428 : ℝ) * 0.001000136222 := by gcongr
      _ ≤ (0.000500052484 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12793 BstLean.Part154.csC) * nuR (rhoBar 12793 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001000136222 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12793 BstLean.Part154.csC) * rhoBar 12793 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000250018428 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000250018428 / 2 + 0.399 * 0.001000136222 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000190965696 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000500052484 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121512754 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000250018428 / 1.414213562 := by gcongr
      _ ≤ (0.000070539101 : ℝ) := by norm_num

end BstLean.Part269.N12793

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12793
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12793 BstLean.Part154.csC) (piBar (rhoBar 12793 BstLean.Part154.csC)) ≤ 1.57488E-7 := by
  have hr0 : 0 ≤ rhoBar 12793 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12793 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12793 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12793 BstLean.Part154.csC) (piBar (rhoBar 12793 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12793 BstLean.Part154.csC) (piBar (rhoBar 12793 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12793 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000190965696 : ℝ) ^ 2 + 0.000121512754 ^ 2 + 3 * 0.000070539101 ^ 2 +
        2 * 0.797885 * 0.000190965696 * 0.000121512754 + 2 * 0.000190965696 * 0.000070539101 +
        4 * 0.797885 * 0.000121512754 * 0.000070539101 := by gcongr
    _ ≤ (1.57488E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12793 BstLean.Part154.csC Θ ≤ 0.002609520594 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12793 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12793 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12793 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12793 BstLean.Part154.csC) (piBar (rhoBar 12793 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12793 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035677681494 * 1.57488E-7 / (0.000250018041 : ℝ) := by gcongr
    _ ≤ 0.002609520594 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12793 BstLean.Part154.csC Θ ≤ 0.002895025557 + 0.000659381628 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12793 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12793 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12793 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035677681494 : ℝ) * ((2 * Θ * 0.000250018428 +
        (6863 / 10000) * 0.000250018428 * 12793 * 0.001000136222) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002895025557 + 0.000659381628 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12793 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12793 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12793 0.011 Θ ∧ gammaRatio 12793 0.011 Θ ≤ 0.000085949871 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12793 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035677681494 : ℝ) * 0.525 / ((1 - 0.011) * 12793) := by gcongr
      _ ≤ (0.000085949871 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12793 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12793 0.011 Θ) :=
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
    badAllowance 12793 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000560204559 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12793 BstLean.Part154.csC) 1.22 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 2 (rhoBar 12793 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12793 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12793 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12793 0.011 Θ) 1.12 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 1 (gammaRatio 12793 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12793 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12793 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12793 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12793 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035677681494 : ℝ) * 12793 *
        (1.8602E-8 / 1.1045361 + 2.2721E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000560204559 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12793 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003455230116 + 0.003268902222 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12793

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12793
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12793 BstLean.Part154.csC) (piBar (rhoBar 12793 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12793 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12793 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12793 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12793 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12793 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12793 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12793 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12793 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12793 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12793 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12793 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12793 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12793 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12793 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052291129994 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12793) ≤ 0.010558556149 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12793 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035677681494)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010558556149 + 2 * 0.737676 / 12793) := by gcongr
    _ ≤ (0.052291129994 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12793 12 ≤ 0.0015 := by
  exact BstLean.Part269.S17.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12793

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12793
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560507743453 : ℝ) ≤ plow 12793 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12793) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052678003783)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001369998312) : eMP 12793 0.011 xi bn ≤ 0.001179569029 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12793 : ℝ) * (1 - 0.011))) ≤ 0.000583244472 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001369998312 / (12793 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000583244472 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000583244472 : ℝ) + 3.141593 * 0.052678003783 / (12793 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001179569029 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052678003783)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001369998312) : PiBarMP 12793 12 0.011 xi bn ≤ 0.160658147704 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12793 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037013488245 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.482340836239 : ℝ) ≤ √((12793 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.106144837493 : ℝ) ≤ √(12793 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12793) ≤ 0.123179941133 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037013488245 + 0.052678003783 * 1.772454 / (2 * (112.482340836239 : ℝ))) * (1 + 0.001179569029) +
        8 / (12793 * 113.106144837493) + 0.123179941133 := by gcongr
    _ ≤ (0.160658147704 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052678003783)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001369998312) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281808022146) :
    parallelOracle 12793 0.011 xi bn cd ≤ 0.161641559947 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12793 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12793 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560507743453 : ℝ) ≤ plow 12793 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.106144837493 : ℝ) ≤ √(12793 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281808022146 : ℝ) / (2 * 0.560507743453 * 113.106144837493)) * 0.160658147704 +
        0.281808022146 ^ 2 / (2 * 0.560507743453 * 113.106144837493) := by gcongr
    _ ≤ (0.161641559947 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052678003783) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001369998312)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281808022146) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12793 12793 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560507743453 : ℝ) ≤ plow 12793 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.106144837493 : ℝ) ≤ √(12793 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12793 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12793 Θ 1.22 ≤ 0.011724389528 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.106144837493 := by gcongr <;> linarith
      _ ≤ (0.011724389528 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12793 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12793 12793 0.011 ≤ 0.008451238470 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12793 12793 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12793 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12793 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12793 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12793 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161641559947 + 0.011724389528 + (0.008451238470 : ℝ) *
        (1 + 2 * (0.281808022146 + 0.011724389528) / (0.560507743453 * 113.106144837493))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12793]

end BstLean.Part269.N12793

/-! The original eight local profiles supply actual 12793 moment certificates. -/
namespace BstLean.Part269.N12793
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12793 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12793 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12793 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052678003783 ∧
    0 ≤ bN 12793 BstLean.Part154.csC (groupTheta g) ∧ bN 12793 BstLean.Part154.csC (groupTheta g) ≤ 0.001369998312 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12793 12793 0.011
      (momentAllowance 12793 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12793 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12793 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12793 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12793 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12793 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229516892152 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12793 0.011
      (momentAllowance 12793 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12793 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12793
/-! The actual computed-centre upper energy formula at 12793. -/
namespace BstLean.Part269.N12793
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12793

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12793
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12793)
open BstLean.Part268 (cell12793)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085223585450
  | 2 => 0.086161536805
  | 3 => 0.087096944357
  | 4 => 0.088031067587
  | 5 => 0.088965434947
  | 6 => 0.089901884457
  | 7 => 0.090842608244
  | 8 => 0.091790201078
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12793 12793 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12793 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003459522332 + 0.003273654356 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S17.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12793

/-! Actual upper energy certificates on all 43 source endpoints at 12793. -/
namespace BstLean.Part269.N12793
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12793)
open BstLean.Part268 (cell12793)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12793 (gMinus 12793) (1 - (cell12793 i).lower) ≤ 1 ∧
    energyUpper 12793 (gMinus 12793) (BstLean.Part211.gPlus 12793)
      (finiteEnergy 12793 12793 0.011) (1 - (cell12793 i).lower) ≤
      (cell12793 i).energy := by
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
      have E := BstLean.Part269.S17.uniformEnergy10 (n := 12793) (by norm_num)
        (q := 1 - (cell12793 ⟨10,by decide⟩).lower)
        (by norm_num [cell12793]) (by norm_num [cell12793])
      exact ⟨E.1,E.2.trans (by norm_num [cell12793])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy11 (n := 12793) (by norm_num)
        (q := 1 - (cell12793 ⟨11,by decide⟩).lower)
        (by norm_num [cell12793]) (by norm_num [cell12793])
      exact ⟨E.1,E.2.trans (by norm_num [cell12793])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy12 (n := 12793) (by norm_num)
        (q := 1 - (cell12793 ⟨12,by decide⟩).lower)
        (by norm_num [cell12793]) (by norm_num [cell12793])
      exact ⟨E.1,E.2.trans (by norm_num [cell12793])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy13 (n := 12793) (by norm_num)
        (q := 1 - (cell12793 ⟨13,by decide⟩).lower)
        (by norm_num [cell12793]) (by norm_num [cell12793])
      exact ⟨E.1,E.2.trans (by norm_num [cell12793])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy14 (n := 12793) (by norm_num)
        (q := 1 - (cell12793 ⟨14,by decide⟩).lower)
        (by norm_num [cell12793]) (by norm_num [cell12793])
      exact ⟨E.1,E.2.trans (by norm_num [cell12793])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy15 (n := 12793) (by norm_num)
        (q := 1 - (cell12793 ⟨15,by decide⟩).lower)
        (by norm_num [cell12793]) (by norm_num [cell12793])
      exact ⟨E.1,E.2.trans (by norm_num [cell12793])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy16 (n := 12793) (by norm_num)
        (q := 1 - (cell12793 ⟨16,by decide⟩).lower)
        (by norm_num [cell12793]) (by norm_num [cell12793])
      exact ⟨E.1,E.2.trans (by norm_num [cell12793])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy17 (n := 12793) (by norm_num)
        (q := 1 - (cell12793 ⟨17,by decide⟩).lower)
        (by norm_num [cell12793]) (by norm_num [cell12793])
      exact ⟨E.1,E.2.trans (by norm_num [cell12793])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy18 (n := 12793) (by norm_num)
        (q := 1 - (cell12793 ⟨18,by decide⟩).lower)
        (by norm_num [cell12793]) (by norm_num [cell12793])
      exact ⟨E.1,E.2.trans (by norm_num [cell12793])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy19 (n := 12793) (by norm_num)
        (q := 1 - (cell12793 ⟨19,by decide⟩).lower)
        (by norm_num [cell12793]) (by norm_num [cell12793])
      exact ⟨E.1,E.2.trans (by norm_num [cell12793])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy20 (n := 12793) (by norm_num)
        (q := 1 - (cell12793 ⟨20,by decide⟩).lower)
        (by norm_num [cell12793]) (by norm_num [cell12793])
      exact ⟨E.1,E.2.trans (by norm_num [cell12793])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy21 (n := 12793) (by norm_num)
        (q := 1 - (cell12793 ⟨21,by decide⟩).lower)
        (by norm_num [cell12793]) (by norm_num [cell12793])
      exact ⟨E.1,E.2.trans (by norm_num [cell12793])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy22 (n := 12793) (by norm_num)
        (q := 1 - (cell12793 ⟨22,by decide⟩).lower)
        (by norm_num [cell12793]) (by norm_num [cell12793])
      exact ⟨E.1,E.2.trans (by norm_num [cell12793])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy23 (n := 12793) (by norm_num)
        (q := 1 - (cell12793 ⟨23,by decide⟩).lower)
        (by norm_num [cell12793]) (by norm_num [cell12793])
      exact ⟨E.1,E.2.trans (by norm_num [cell12793])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy24 (n := 12793) (by norm_num)
        (q := 1 - (cell12793 ⟨24,by decide⟩).lower)
        (by norm_num [cell12793]) (by norm_num [cell12793])
      exact ⟨E.1,E.2.trans (by norm_num [cell12793])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy25 (n := 12793) (by norm_num)
        (q := 1 - (cell12793 ⟨25,by decide⟩).lower)
        (by norm_num [cell12793]) (by norm_num [cell12793])
      exact ⟨E.1,E.2.trans (by norm_num [cell12793])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy26 (n := 12793) (by norm_num)
        (q := 1 - (cell12793 ⟨26,by decide⟩).lower)
        (by norm_num [cell12793]) (by norm_num [cell12793])
      exact ⟨E.1,E.2.trans (by norm_num [cell12793])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy27 (n := 12793) (by norm_num)
        (q := 1 - (cell12793 ⟨27,by decide⟩).lower)
        (by norm_num [cell12793]) (by norm_num [cell12793])
      exact ⟨E.1,E.2.trans (by norm_num [cell12793])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy28 (n := 12793) (by norm_num)
        (q := 1 - (cell12793 ⟨28,by decide⟩).lower)
        (by norm_num [cell12793]) (by norm_num [cell12793])
      exact ⟨E.1,E.2.trans (by norm_num [cell12793])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy29 (n := 12793) (by norm_num)
        (q := 1 - (cell12793 ⟨29,by decide⟩).lower)
        (by norm_num [cell12793]) (by norm_num [cell12793])
      exact ⟨E.1,E.2.trans (by norm_num [cell12793])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy30 (n := 12793) (by norm_num)
        (q := 1 - (cell12793 ⟨30,by decide⟩).lower)
        (by norm_num [cell12793]) (by norm_num [cell12793])
      exact ⟨E.1,E.2.trans (by norm_num [cell12793])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy31 (n := 12793) (by norm_num)
        (q := 1 - (cell12793 ⟨31,by decide⟩).lower)
        (by norm_num [cell12793]) (by norm_num [cell12793])
      exact ⟨E.1,E.2.trans (by norm_num [cell12793])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy32 (n := 12793) (by norm_num)
        (q := 1 - (cell12793 ⟨32,by decide⟩).lower)
        (by norm_num [cell12793]) (by norm_num [cell12793])
      exact ⟨E.1,E.2.trans (by norm_num [cell12793])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy33 (n := 12793) (by norm_num)
        (q := 1 - (cell12793 ⟨33,by decide⟩).lower)
        (by norm_num [cell12793]) (by norm_num [cell12793])
      exact ⟨E.1,E.2.trans (by norm_num [cell12793])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy34 (n := 12793) (by norm_num)
        (q := 1 - (cell12793 ⟨34,by decide⟩).lower)
        (by norm_num [cell12793]) (by norm_num [cell12793])
      exact ⟨E.1,E.2.trans (by norm_num [cell12793])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy35 (n := 12793) (by norm_num)
        (q := 1 - (cell12793 ⟨35,by decide⟩).lower)
        (by norm_num [cell12793]) (by norm_num [cell12793])
      exact ⟨E.1,E.2.trans (by norm_num [cell12793])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy36 (n := 12793) (by norm_num)
        (q := 1 - (cell12793 ⟨36,by decide⟩).lower)
        (by norm_num [cell12793]) (by norm_num [cell12793])
      exact ⟨E.1,E.2.trans (by norm_num [cell12793])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy37 (n := 12793) (by norm_num)
        (q := 1 - (cell12793 ⟨37,by decide⟩).lower)
        (by norm_num [cell12793]) (by norm_num [cell12793])
      exact ⟨E.1,E.2.trans (by norm_num [cell12793])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy38 (n := 12793) (by norm_num)
        (q := 1 - (cell12793 ⟨38,by decide⟩).lower)
        (by norm_num [cell12793]) (by norm_num [cell12793])
      exact ⟨E.1,E.2.trans (by norm_num [cell12793])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy39 (n := 12793) (by norm_num)
        (q := 1 - (cell12793 ⟨39,by decide⟩).lower)
        (by norm_num [cell12793]) (by norm_num [cell12793])
      exact ⟨E.1,E.2.trans (by norm_num [cell12793])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy40 (n := 12793) (by norm_num)
        (q := 1 - (cell12793 ⟨40,by decide⟩).lower)
        (by norm_num [cell12793]) (by norm_num [cell12793])
      exact ⟨E.1,E.2.trans (by norm_num [cell12793])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy41 (n := 12793) (by norm_num)
        (q := 1 - (cell12793 ⟨41,by decide⟩).lower)
        (by norm_num [cell12793]) (by norm_num [cell12793])
      exact ⟨E.1,E.2.trans (by norm_num [cell12793])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy42 (n := 12793) (by norm_num)
        (q := 1 - (cell12793 ⟨42,by decide⟩).lower)
        (by norm_num [cell12793]) (by norm_num [cell12793])
      exact ⟨E.1,E.2.trans (by norm_num [cell12793])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy43 (n := 12793) (by norm_num)
        (q := 1 - (cell12793 ⟨43,by decide⟩).lower)
        (by norm_num [cell12793]) (by norm_num [cell12793])
      exact ⟨E.1,E.2.trans (by norm_num [cell12793])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy44 (n := 12793) (by norm_num)
        (q := 1 - (cell12793 ⟨44,by decide⟩).lower)
        (by norm_num [cell12793]) (by norm_num [cell12793])
      exact ⟨E.1,E.2.trans (by norm_num [cell12793])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy45 (n := 12793) (by norm_num)
        (q := 1 - (cell12793 ⟨45,by decide⟩).lower)
        (by norm_num [cell12793]) (by norm_num [cell12793])
      exact ⟨E.1,E.2.trans (by norm_num [cell12793])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy46 (n := 12793) (by norm_num)
        (q := 1 - (cell12793 ⟨46,by decide⟩).lower)
        (by norm_num [cell12793]) (by norm_num [cell12793])
      exact ⟨E.1,E.2.trans (by norm_num [cell12793])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy47 (n := 12793) (by norm_num)
        (q := 1 - (cell12793 ⟨47,by decide⟩).lower)
        (by norm_num [cell12793]) (by norm_num [cell12793])
      exact ⟨E.1,E.2.trans (by norm_num [cell12793])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy48 (n := 12793) (by norm_num)
        (q := 1 - (cell12793 ⟨48,by decide⟩).lower)
        (by norm_num [cell12793]) (by norm_num [cell12793])
      exact ⟨E.1,E.2.trans (by norm_num [cell12793])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy49 (n := 12793) (by norm_num)
        (q := 1 - (cell12793 ⟨49,by decide⟩).lower)
        (by norm_num [cell12793]) (by norm_num [cell12793])
      exact ⟨E.1,E.2.trans (by norm_num [cell12793])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy50 (n := 12793) (by norm_num)
        (q := 1 - (cell12793 ⟨50,by decide⟩).lower)
        (by norm_num [cell12793]) (by norm_num [cell12793])
      exact ⟨E.1,E.2.trans (by norm_num [cell12793])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy51 (n := 12793) (by norm_num)
        (q := 1 - (cell12793 ⟨51,by decide⟩).lower)
        (by norm_num [cell12793]) (by norm_num [cell12793])
      exact ⟨E.1,E.2.trans (by norm_num [cell12793])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy52 (n := 12793) (by norm_num)
        (q := 1 - (cell12793 ⟨52,by decide⟩).lower)
        (by norm_num [cell12793]) (by norm_num [cell12793])
      exact ⟨E.1,E.2.trans (by norm_num [cell12793])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12793

/-! Source-cell containment and simple scalar guards at 12793. -/
namespace BstLean.Part269.N12793
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12793)
open BstLean.Part268 (cell12793)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12793 ⟨10,by decide⟩).lower ∧ (cell12793 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12793 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12793 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12793 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12793 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12793 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12793,cell12793,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12793 ⟨11,by decide⟩).lower ∧ (cell12793 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12793 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12793 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12793 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12793 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12793 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12793,cell12793,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12793 ⟨12,by decide⟩).lower ∧ (cell12793 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12793 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12793 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12793 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12793 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12793 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12793,cell12793,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12793 ⟨13,by decide⟩).lower ∧ (cell12793 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12793 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12793 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12793 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12793 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12793 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12793,cell12793,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12793 ⟨14,by decide⟩).lower ∧ (cell12793 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12793 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12793 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12793 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12793 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12793 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12793,cell12793,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12793 ⟨15,by decide⟩).lower ∧ (cell12793 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12793 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12793 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12793 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12793 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12793 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12793,cell12793,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12793 ⟨16,by decide⟩).lower ∧ (cell12793 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12793 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12793 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12793 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12793 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12793 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12793,cell12793,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12793 ⟨17,by decide⟩).lower ∧ (cell12793 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12793 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12793 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12793 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12793 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12793 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12793,cell12793,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12793 ⟨18,by decide⟩).lower ∧ (cell12793 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12793 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12793 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12793 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12793 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12793 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12793,cell12793,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12793 ⟨19,by decide⟩).lower ∧ (cell12793 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12793 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12793 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12793 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12793 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12793 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12793,cell12793,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12793 ⟨20,by decide⟩).lower ∧ (cell12793 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12793 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12793 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12793 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12793 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12793 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12793,cell12793,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12793 ⟨21,by decide⟩).lower ∧ (cell12793 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12793 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12793 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12793 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12793 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12793 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12793,cell12793,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12793 ⟨22,by decide⟩).lower ∧ (cell12793 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12793 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12793 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12793 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12793 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12793 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12793,cell12793,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12793 ⟨23,by decide⟩).lower ∧ (cell12793 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12793 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12793 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12793 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12793 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12793 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12793,cell12793,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12793 ⟨24,by decide⟩).lower ∧ (cell12793 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12793 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12793 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12793 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12793 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12793 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12793,cell12793,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12793 ⟨25,by decide⟩).lower ∧ (cell12793 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12793 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12793 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12793 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12793 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12793 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12793,cell12793,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12793 ⟨26,by decide⟩).lower ∧ (cell12793 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12793 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12793 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12793 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12793 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12793 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12793,cell12793,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12793 ⟨27,by decide⟩).lower ∧ (cell12793 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12793 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12793 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12793 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12793 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12793 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12793,cell12793,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12793 ⟨28,by decide⟩).lower ∧ (cell12793 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12793 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12793 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12793 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12793 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12793 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12793,cell12793,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12793 ⟨29,by decide⟩).lower ∧ (cell12793 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12793 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12793 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12793 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12793 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12793 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12793,cell12793,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12793 ⟨30,by decide⟩).lower ∧ (cell12793 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12793 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12793 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12793 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12793 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12793 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12793,cell12793,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12793 ⟨31,by decide⟩).lower ∧ (cell12793 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12793 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12793 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12793 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12793 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12793 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12793,cell12793,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12793 ⟨32,by decide⟩).lower ∧ (cell12793 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12793 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12793 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12793 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12793 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12793 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12793,cell12793,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12793 ⟨33,by decide⟩).lower ∧ (cell12793 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12793 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12793 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12793 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12793 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12793 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12793,cell12793,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12793 ⟨34,by decide⟩).lower ∧ (cell12793 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12793 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12793 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12793 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12793 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12793 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12793,cell12793,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12793 ⟨35,by decide⟩).lower ∧ (cell12793 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12793 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12793 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12793 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12793 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12793 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12793,cell12793,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12793 ⟨36,by decide⟩).lower ∧ (cell12793 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12793 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12793 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12793 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12793 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12793 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12793,cell12793,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12793 ⟨37,by decide⟩).lower ∧ (cell12793 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12793 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12793 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12793 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12793 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12793 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12793,cell12793,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12793 ⟨38,by decide⟩).lower ∧ (cell12793 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12793 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12793 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12793 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12793 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12793 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12793,cell12793,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12793 ⟨39,by decide⟩).lower ∧ (cell12793 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12793 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12793 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12793 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12793 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12793 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12793,cell12793,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12793 ⟨40,by decide⟩).lower ∧ (cell12793 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12793 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12793 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12793 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12793 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12793 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12793,cell12793,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12793 ⟨41,by decide⟩).lower ∧ (cell12793 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12793 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12793 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12793 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12793 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12793 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12793,cell12793,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12793 ⟨42,by decide⟩).lower ∧ (cell12793 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12793 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12793 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12793 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12793 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12793 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12793,cell12793,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12793 ⟨43,by decide⟩).lower ∧ (cell12793 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12793 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12793 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12793 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12793 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12793 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12793,cell12793,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12793 ⟨44,by decide⟩).lower ∧ (cell12793 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12793 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12793 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12793 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12793 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12793 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12793,cell12793,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12793 ⟨45,by decide⟩).lower ∧ (cell12793 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12793 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12793 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12793 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12793 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12793 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12793,cell12793,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12793 ⟨46,by decide⟩).lower ∧ (cell12793 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12793 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12793 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12793 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12793 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12793 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12793,cell12793,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12793 ⟨47,by decide⟩).lower ∧ (cell12793 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12793 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12793 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12793 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12793 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12793 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12793,cell12793,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12793 ⟨48,by decide⟩).lower ∧ (cell12793 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12793 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12793 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12793 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12793 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12793 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12793,cell12793,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12793 ⟨49,by decide⟩).lower ∧ (cell12793 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12793 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12793 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12793 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12793 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12793 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12793,cell12793,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12793 ⟨50,by decide⟩).lower ∧ (cell12793 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12793 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12793 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12793 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12793 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12793 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12793,cell12793,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12793 ⟨51,by decide⟩).lower ∧ (cell12793 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12793 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12793 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12793 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12793 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12793 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12793,cell12793,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12793 ⟨52,by decide⟩).lower ∧ (cell12793 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12793 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12793 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12793 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12793 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12793 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12793,cell12793,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12793 i).lower ∧
    (cell12793 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12793 i).upper ≤ (0.532 : ℝ) ∧
    (cell12793 i).centre ≤ (0.1 : ℝ) ∧ (cell12793 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12793 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12793 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12793

/-! The local source numeric instances at 12793 have no network premises. -/
namespace BstLean.Part269.N12793
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12793)
open BstLean.Part268 (cell12793)

noncomputable def sourceNumerics12793 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12793 (cell12793 i)
      scalarRow12793.M scalarRow12793.H scalarRow12793.xi := by
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
    energy_allowance := scalarRow12793.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12793]
    centre_nonneg := (scalarRow12793.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D17.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12793])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12793
/-! Actual 12794 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12794
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12794 ≤ (1.035676274935 : ℝ) := by
  have hr : (113.110565377421 : ℝ) ≤ √(12794 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.110565377421 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12794 12794 (11 / 1000) ≤
    (0.008450908179 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12794) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.110565377421 : ℝ) ≤ √(12794 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12794)
  have hdiv : K / √(12794 : ℝ) ≤ K / 113.110565377421 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.110565377421 ≤ (0.008450908179 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12794.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12794 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12794 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12794 := gPlus_lower 12794
end BstLean.Part269.N12794

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12794
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035676274934 : ℝ) ≤ wn 12794 := by
  have hn : √(12794 : ℝ) ≤ 113.110565377422 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12794 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.110565377422 ≤ 2 / √(12794 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000249998160 : ℝ) ≤ rhoBar 12794 BstLean.Part154.csC ∧
    rhoBar 12794 BstLean.Part154.csC ≤ 0.000249998547 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035676274934 : ℝ) / (1.295212 * 12794) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035676274935 : ℝ) / (1.29521 * 12794) := by gcongr
      _ ≤ (0.000249998547 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12794 BstLean.Part154.csC) ≤ 0.001000056688 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12794 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12794 BstLean.Part154.csC) (piBar (rhoBar 12794 BstLean.Part154.csC)) ≤ 0.000190950510 ∧
    cc1 (rhoBar 12794 BstLean.Part154.csC) (piBar (rhoBar 12794 BstLean.Part154.csC)) ≤ 0.000121503091 ∧
    cc2 (rhoBar 12794 BstLean.Part154.csC) ≤ 0.000070533492 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12794 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12794 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12794 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12794 BstLean.Part154.csC * nuR (rhoBar 12794 BstLean.Part154.csC)) ≤ 0.000500012719 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000249998547 : ℝ) * 0.001000056688 := by gcongr
      _ ≤ (0.000500012719 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12794 BstLean.Part154.csC) * nuR (rhoBar 12794 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001000056688 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12794 BstLean.Part154.csC) * rhoBar 12794 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000249998547 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000249998547 / 2 + 0.399 * 0.001000056688 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000190950510 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000500012719 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121503091 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000249998547 / 1.414213562 := by gcongr
      _ ≤ (0.000070533492 : ℝ) := by norm_num

end BstLean.Part269.N12794

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12794
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12794 BstLean.Part154.csC) (piBar (rhoBar 12794 BstLean.Part154.csC)) ≤ 1.57463E-7 := by
  have hr0 : 0 ≤ rhoBar 12794 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12794 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12794 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12794 BstLean.Part154.csC) (piBar (rhoBar 12794 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12794 BstLean.Part154.csC) (piBar (rhoBar 12794 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12794 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000190950510 : ℝ) ^ 2 + 0.000121503091 ^ 2 + 3 * 0.000070533492 ^ 2 +
        2 * 0.797885 * 0.000190950510 * 0.000121503091 + 2 * 0.000190950510 * 0.000070533492 +
        4 * 0.797885 * 0.000121503091 * 0.000070533492 := by gcongr
    _ ≤ (1.57463E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12794 BstLean.Part154.csC Θ ≤ 0.002609310298 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12794 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12794 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12794 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12794 BstLean.Part154.csC) (piBar (rhoBar 12794 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12794 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035676274935 * 1.57463E-7 / (0.000249998160 : ℝ) := by gcongr
    _ ≤ 0.002609310298 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12794 BstLean.Part154.csC Θ ≤ 0.002894787476 + 0.000659328300 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12794 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12794 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12794 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035676274935 : ℝ) * ((2 * Θ * 0.000249998547 +
        (6863 / 10000) * 0.000249998547 * 12794 * 0.001000056688) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002894787476 + 0.000659328300 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12794 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12794 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12794 0.011 Θ ∧ gammaRatio 12794 0.011 Θ ≤ 0.000085943036 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12794 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035676274935 : ℝ) * 0.525 / ((1 - 0.011) * 12794) := by gcongr
      _ ≤ (0.000085943036 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12794 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12794 0.011 Θ) :=
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
    badAllowance 12794 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000560204559 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12794 BstLean.Part154.csC) 1.22 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 2 (rhoBar 12794 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12794 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12794 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12794 0.011 Θ) 1.12 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 1 (gammaRatio 12794 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12794 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12794 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12794 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12794 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035676274935 : ℝ) * 12794 *
        (1.8602E-8 / 1.1045361 + 2.2721E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000560204559 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12794 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003454992035 + 0.003268638598 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12794

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12794
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12794 BstLean.Part154.csC) (piBar (rhoBar 12794 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12794 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12794 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12794 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12794 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12794 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12794 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12794 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12794 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12794 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12794 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12794 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12794 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12794 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12794 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052289064295 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12794) ≤ 0.010558143504 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12794 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035676274935)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010558143504 + 2 * 0.737676 / 12794) := by gcongr
    _ ≤ (0.052289064295 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12794 12 ≤ 0.0015 := by
  exact BstLean.Part269.S17.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12794

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12794
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560507788017 : ℝ) ≤ plow 12794 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12794) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052677627299)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001369887907) : eMP 12794 0.011 xi bn ≤ 0.001179475323 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12794 : ℝ) * (1 - 0.011))) ≤ 0.000583198177 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001369887907 / (12794 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000583198177 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000583198177 : ℝ) + 3.141593 * 0.052677627299 / (12794 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001179475323 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052677627299)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001369887907) : PiBarMP 12794 12 0.011 xi bn ≤ 0.160651817067 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12794 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037011996799 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.486736995967 : ℝ) ≤ √((12794 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.110565377421 : ℝ) ≤ √(12794 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12794) ≤ 0.123175127065 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037011996799 + 0.052677627299 * 1.772454 / (2 * (112.486736995967 : ℝ))) * (1 + 0.001179475323) +
        8 / (12794 * 113.110565377421) + 0.123175127065 := by gcongr
    _ ≤ (0.160651817067 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052677627299)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001369887907) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281805136280) :
    parallelOracle 12794 0.011 xi bn cd ≤ 0.161635160245 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12794 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12794 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560507788017 : ℝ) ≤ plow 12794 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.110565377421 : ℝ) ≤ √(12794 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281805136280 : ℝ) / (2 * 0.560507788017 * 113.110565377421)) * 0.160651817067 +
        0.281805136280 ^ 2 / (2 * 0.560507788017 * 113.110565377421) := by gcongr
    _ ≤ (0.161635160245 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052677627299) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001369887907)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281805136280) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12794 12794 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560507788017 : ℝ) ≤ plow 12794 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.110565377421 : ℝ) ≤ √(12794 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12794 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12794 Θ 1.22 ≤ 0.011723931320 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.110565377421 := by gcongr <;> linarith
      _ ≤ (0.011723931320 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12794 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12794 12794 0.011 ≤ 0.008450908179 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12794 12794 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12794 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12794 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12794 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12794 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161635160245 + 0.011723931320 + (0.008450908179 : ℝ) *
        (1 + 2 * (0.281805136280 + 0.011723931320) / (0.560507788017 * 113.110565377421))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12794]

end BstLean.Part269.N12794

/-! The original eight local profiles supply actual 12794 moment certificates. -/
namespace BstLean.Part269.N12794
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12794 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12794 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12794 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052677627299 ∧
    0 ≤ bN 12794 BstLean.Part154.csC (groupTheta g) ∧ bN 12794 BstLean.Part154.csC (groupTheta g) ≤ 0.001369887907 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12794 12794 0.011
      (momentAllowance 12794 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12794 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12794 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12794 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12794 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12794 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229516071985 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12794 0.011
      (momentAllowance 12794 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12794 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12794
/-! The actual computed-centre upper energy formula at 12794. -/
namespace BstLean.Part269.N12794
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12794

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12794
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12794)
open BstLean.Part268 (cell12794)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085220765892
  | 2 => 0.086158667586
  | 3 => 0.087094018583
  | 4 => 0.088028076750
  | 5 => 0.088962368640
  | 6 => 0.089898730046
  | 7 => 0.090839350505
  | 8 => 0.091786821790
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12794 12794 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12794 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003459522332 + 0.003273654356 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S17.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12794

/-! Actual upper energy certificates on all 43 source endpoints at 12794. -/
namespace BstLean.Part269.N12794
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12794)
open BstLean.Part268 (cell12794)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12794 (gMinus 12794) (1 - (cell12794 i).lower) ≤ 1 ∧
    energyUpper 12794 (gMinus 12794) (BstLean.Part211.gPlus 12794)
      (finiteEnergy 12794 12794 0.011) (1 - (cell12794 i).lower) ≤
      (cell12794 i).energy := by
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
      have E := BstLean.Part269.S17.uniformEnergy10 (n := 12794) (by norm_num)
        (q := 1 - (cell12794 ⟨10,by decide⟩).lower)
        (by norm_num [cell12794]) (by norm_num [cell12794])
      exact ⟨E.1,E.2.trans (by norm_num [cell12794])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy11 (n := 12794) (by norm_num)
        (q := 1 - (cell12794 ⟨11,by decide⟩).lower)
        (by norm_num [cell12794]) (by norm_num [cell12794])
      exact ⟨E.1,E.2.trans (by norm_num [cell12794])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy12 (n := 12794) (by norm_num)
        (q := 1 - (cell12794 ⟨12,by decide⟩).lower)
        (by norm_num [cell12794]) (by norm_num [cell12794])
      exact ⟨E.1,E.2.trans (by norm_num [cell12794])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy13 (n := 12794) (by norm_num)
        (q := 1 - (cell12794 ⟨13,by decide⟩).lower)
        (by norm_num [cell12794]) (by norm_num [cell12794])
      exact ⟨E.1,E.2.trans (by norm_num [cell12794])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy14 (n := 12794) (by norm_num)
        (q := 1 - (cell12794 ⟨14,by decide⟩).lower)
        (by norm_num [cell12794]) (by norm_num [cell12794])
      exact ⟨E.1,E.2.trans (by norm_num [cell12794])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy15 (n := 12794) (by norm_num)
        (q := 1 - (cell12794 ⟨15,by decide⟩).lower)
        (by norm_num [cell12794]) (by norm_num [cell12794])
      exact ⟨E.1,E.2.trans (by norm_num [cell12794])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy16 (n := 12794) (by norm_num)
        (q := 1 - (cell12794 ⟨16,by decide⟩).lower)
        (by norm_num [cell12794]) (by norm_num [cell12794])
      exact ⟨E.1,E.2.trans (by norm_num [cell12794])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy17 (n := 12794) (by norm_num)
        (q := 1 - (cell12794 ⟨17,by decide⟩).lower)
        (by norm_num [cell12794]) (by norm_num [cell12794])
      exact ⟨E.1,E.2.trans (by norm_num [cell12794])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy18 (n := 12794) (by norm_num)
        (q := 1 - (cell12794 ⟨18,by decide⟩).lower)
        (by norm_num [cell12794]) (by norm_num [cell12794])
      exact ⟨E.1,E.2.trans (by norm_num [cell12794])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy19 (n := 12794) (by norm_num)
        (q := 1 - (cell12794 ⟨19,by decide⟩).lower)
        (by norm_num [cell12794]) (by norm_num [cell12794])
      exact ⟨E.1,E.2.trans (by norm_num [cell12794])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy20 (n := 12794) (by norm_num)
        (q := 1 - (cell12794 ⟨20,by decide⟩).lower)
        (by norm_num [cell12794]) (by norm_num [cell12794])
      exact ⟨E.1,E.2.trans (by norm_num [cell12794])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy21 (n := 12794) (by norm_num)
        (q := 1 - (cell12794 ⟨21,by decide⟩).lower)
        (by norm_num [cell12794]) (by norm_num [cell12794])
      exact ⟨E.1,E.2.trans (by norm_num [cell12794])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy22 (n := 12794) (by norm_num)
        (q := 1 - (cell12794 ⟨22,by decide⟩).lower)
        (by norm_num [cell12794]) (by norm_num [cell12794])
      exact ⟨E.1,E.2.trans (by norm_num [cell12794])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy23 (n := 12794) (by norm_num)
        (q := 1 - (cell12794 ⟨23,by decide⟩).lower)
        (by norm_num [cell12794]) (by norm_num [cell12794])
      exact ⟨E.1,E.2.trans (by norm_num [cell12794])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy24 (n := 12794) (by norm_num)
        (q := 1 - (cell12794 ⟨24,by decide⟩).lower)
        (by norm_num [cell12794]) (by norm_num [cell12794])
      exact ⟨E.1,E.2.trans (by norm_num [cell12794])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy25 (n := 12794) (by norm_num)
        (q := 1 - (cell12794 ⟨25,by decide⟩).lower)
        (by norm_num [cell12794]) (by norm_num [cell12794])
      exact ⟨E.1,E.2.trans (by norm_num [cell12794])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy26 (n := 12794) (by norm_num)
        (q := 1 - (cell12794 ⟨26,by decide⟩).lower)
        (by norm_num [cell12794]) (by norm_num [cell12794])
      exact ⟨E.1,E.2.trans (by norm_num [cell12794])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy27 (n := 12794) (by norm_num)
        (q := 1 - (cell12794 ⟨27,by decide⟩).lower)
        (by norm_num [cell12794]) (by norm_num [cell12794])
      exact ⟨E.1,E.2.trans (by norm_num [cell12794])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy28 (n := 12794) (by norm_num)
        (q := 1 - (cell12794 ⟨28,by decide⟩).lower)
        (by norm_num [cell12794]) (by norm_num [cell12794])
      exact ⟨E.1,E.2.trans (by norm_num [cell12794])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy29 (n := 12794) (by norm_num)
        (q := 1 - (cell12794 ⟨29,by decide⟩).lower)
        (by norm_num [cell12794]) (by norm_num [cell12794])
      exact ⟨E.1,E.2.trans (by norm_num [cell12794])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy30 (n := 12794) (by norm_num)
        (q := 1 - (cell12794 ⟨30,by decide⟩).lower)
        (by norm_num [cell12794]) (by norm_num [cell12794])
      exact ⟨E.1,E.2.trans (by norm_num [cell12794])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy31 (n := 12794) (by norm_num)
        (q := 1 - (cell12794 ⟨31,by decide⟩).lower)
        (by norm_num [cell12794]) (by norm_num [cell12794])
      exact ⟨E.1,E.2.trans (by norm_num [cell12794])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy32 (n := 12794) (by norm_num)
        (q := 1 - (cell12794 ⟨32,by decide⟩).lower)
        (by norm_num [cell12794]) (by norm_num [cell12794])
      exact ⟨E.1,E.2.trans (by norm_num [cell12794])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy33 (n := 12794) (by norm_num)
        (q := 1 - (cell12794 ⟨33,by decide⟩).lower)
        (by norm_num [cell12794]) (by norm_num [cell12794])
      exact ⟨E.1,E.2.trans (by norm_num [cell12794])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy34 (n := 12794) (by norm_num)
        (q := 1 - (cell12794 ⟨34,by decide⟩).lower)
        (by norm_num [cell12794]) (by norm_num [cell12794])
      exact ⟨E.1,E.2.trans (by norm_num [cell12794])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy35 (n := 12794) (by norm_num)
        (q := 1 - (cell12794 ⟨35,by decide⟩).lower)
        (by norm_num [cell12794]) (by norm_num [cell12794])
      exact ⟨E.1,E.2.trans (by norm_num [cell12794])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy36 (n := 12794) (by norm_num)
        (q := 1 - (cell12794 ⟨36,by decide⟩).lower)
        (by norm_num [cell12794]) (by norm_num [cell12794])
      exact ⟨E.1,E.2.trans (by norm_num [cell12794])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy37 (n := 12794) (by norm_num)
        (q := 1 - (cell12794 ⟨37,by decide⟩).lower)
        (by norm_num [cell12794]) (by norm_num [cell12794])
      exact ⟨E.1,E.2.trans (by norm_num [cell12794])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy38 (n := 12794) (by norm_num)
        (q := 1 - (cell12794 ⟨38,by decide⟩).lower)
        (by norm_num [cell12794]) (by norm_num [cell12794])
      exact ⟨E.1,E.2.trans (by norm_num [cell12794])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy39 (n := 12794) (by norm_num)
        (q := 1 - (cell12794 ⟨39,by decide⟩).lower)
        (by norm_num [cell12794]) (by norm_num [cell12794])
      exact ⟨E.1,E.2.trans (by norm_num [cell12794])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy40 (n := 12794) (by norm_num)
        (q := 1 - (cell12794 ⟨40,by decide⟩).lower)
        (by norm_num [cell12794]) (by norm_num [cell12794])
      exact ⟨E.1,E.2.trans (by norm_num [cell12794])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy41 (n := 12794) (by norm_num)
        (q := 1 - (cell12794 ⟨41,by decide⟩).lower)
        (by norm_num [cell12794]) (by norm_num [cell12794])
      exact ⟨E.1,E.2.trans (by norm_num [cell12794])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy42 (n := 12794) (by norm_num)
        (q := 1 - (cell12794 ⟨42,by decide⟩).lower)
        (by norm_num [cell12794]) (by norm_num [cell12794])
      exact ⟨E.1,E.2.trans (by norm_num [cell12794])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy43 (n := 12794) (by norm_num)
        (q := 1 - (cell12794 ⟨43,by decide⟩).lower)
        (by norm_num [cell12794]) (by norm_num [cell12794])
      exact ⟨E.1,E.2.trans (by norm_num [cell12794])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy44 (n := 12794) (by norm_num)
        (q := 1 - (cell12794 ⟨44,by decide⟩).lower)
        (by norm_num [cell12794]) (by norm_num [cell12794])
      exact ⟨E.1,E.2.trans (by norm_num [cell12794])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy45 (n := 12794) (by norm_num)
        (q := 1 - (cell12794 ⟨45,by decide⟩).lower)
        (by norm_num [cell12794]) (by norm_num [cell12794])
      exact ⟨E.1,E.2.trans (by norm_num [cell12794])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy46 (n := 12794) (by norm_num)
        (q := 1 - (cell12794 ⟨46,by decide⟩).lower)
        (by norm_num [cell12794]) (by norm_num [cell12794])
      exact ⟨E.1,E.2.trans (by norm_num [cell12794])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy47 (n := 12794) (by norm_num)
        (q := 1 - (cell12794 ⟨47,by decide⟩).lower)
        (by norm_num [cell12794]) (by norm_num [cell12794])
      exact ⟨E.1,E.2.trans (by norm_num [cell12794])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy48 (n := 12794) (by norm_num)
        (q := 1 - (cell12794 ⟨48,by decide⟩).lower)
        (by norm_num [cell12794]) (by norm_num [cell12794])
      exact ⟨E.1,E.2.trans (by norm_num [cell12794])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy49 (n := 12794) (by norm_num)
        (q := 1 - (cell12794 ⟨49,by decide⟩).lower)
        (by norm_num [cell12794]) (by norm_num [cell12794])
      exact ⟨E.1,E.2.trans (by norm_num [cell12794])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy50 (n := 12794) (by norm_num)
        (q := 1 - (cell12794 ⟨50,by decide⟩).lower)
        (by norm_num [cell12794]) (by norm_num [cell12794])
      exact ⟨E.1,E.2.trans (by norm_num [cell12794])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy51 (n := 12794) (by norm_num)
        (q := 1 - (cell12794 ⟨51,by decide⟩).lower)
        (by norm_num [cell12794]) (by norm_num [cell12794])
      exact ⟨E.1,E.2.trans (by norm_num [cell12794])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy52 (n := 12794) (by norm_num)
        (q := 1 - (cell12794 ⟨52,by decide⟩).lower)
        (by norm_num [cell12794]) (by norm_num [cell12794])
      exact ⟨E.1,E.2.trans (by norm_num [cell12794])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12794

/-! Source-cell containment and simple scalar guards at 12794. -/
namespace BstLean.Part269.N12794
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12794)
open BstLean.Part268 (cell12794)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12794 ⟨10,by decide⟩).lower ∧ (cell12794 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12794 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12794 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12794 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12794 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12794 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12794,cell12794,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12794 ⟨11,by decide⟩).lower ∧ (cell12794 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12794 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12794 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12794 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12794 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12794 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12794,cell12794,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12794 ⟨12,by decide⟩).lower ∧ (cell12794 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12794 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12794 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12794 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12794 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12794 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12794,cell12794,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12794 ⟨13,by decide⟩).lower ∧ (cell12794 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12794 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12794 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12794 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12794 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12794 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12794,cell12794,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12794 ⟨14,by decide⟩).lower ∧ (cell12794 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12794 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12794 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12794 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12794 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12794 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12794,cell12794,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12794 ⟨15,by decide⟩).lower ∧ (cell12794 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12794 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12794 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12794 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12794 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12794 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12794,cell12794,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12794 ⟨16,by decide⟩).lower ∧ (cell12794 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12794 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12794 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12794 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12794 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12794 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12794,cell12794,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12794 ⟨17,by decide⟩).lower ∧ (cell12794 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12794 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12794 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12794 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12794 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12794 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12794,cell12794,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12794 ⟨18,by decide⟩).lower ∧ (cell12794 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12794 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12794 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12794 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12794 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12794 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12794,cell12794,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12794 ⟨19,by decide⟩).lower ∧ (cell12794 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12794 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12794 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12794 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12794 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12794 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12794,cell12794,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12794 ⟨20,by decide⟩).lower ∧ (cell12794 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12794 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12794 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12794 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12794 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12794 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12794,cell12794,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12794 ⟨21,by decide⟩).lower ∧ (cell12794 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12794 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12794 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12794 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12794 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12794 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12794,cell12794,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12794 ⟨22,by decide⟩).lower ∧ (cell12794 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12794 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12794 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12794 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12794 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12794 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12794,cell12794,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12794 ⟨23,by decide⟩).lower ∧ (cell12794 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12794 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12794 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12794 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12794 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12794 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12794,cell12794,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12794 ⟨24,by decide⟩).lower ∧ (cell12794 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12794 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12794 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12794 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12794 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12794 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12794,cell12794,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12794 ⟨25,by decide⟩).lower ∧ (cell12794 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12794 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12794 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12794 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12794 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12794 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12794,cell12794,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12794 ⟨26,by decide⟩).lower ∧ (cell12794 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12794 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12794 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12794 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12794 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12794 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12794,cell12794,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12794 ⟨27,by decide⟩).lower ∧ (cell12794 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12794 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12794 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12794 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12794 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12794 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12794,cell12794,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12794 ⟨28,by decide⟩).lower ∧ (cell12794 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12794 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12794 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12794 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12794 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12794 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12794,cell12794,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12794 ⟨29,by decide⟩).lower ∧ (cell12794 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12794 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12794 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12794 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12794 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12794 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12794,cell12794,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12794 ⟨30,by decide⟩).lower ∧ (cell12794 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12794 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12794 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12794 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12794 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12794 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12794,cell12794,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12794 ⟨31,by decide⟩).lower ∧ (cell12794 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12794 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12794 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12794 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12794 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12794 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12794,cell12794,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12794 ⟨32,by decide⟩).lower ∧ (cell12794 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12794 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12794 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12794 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12794 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12794 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12794,cell12794,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12794 ⟨33,by decide⟩).lower ∧ (cell12794 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12794 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12794 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12794 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12794 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12794 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12794,cell12794,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12794 ⟨34,by decide⟩).lower ∧ (cell12794 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12794 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12794 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12794 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12794 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12794 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12794,cell12794,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12794 ⟨35,by decide⟩).lower ∧ (cell12794 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12794 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12794 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12794 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12794 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12794 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12794,cell12794,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12794 ⟨36,by decide⟩).lower ∧ (cell12794 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12794 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12794 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12794 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12794 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12794 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12794,cell12794,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12794 ⟨37,by decide⟩).lower ∧ (cell12794 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12794 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12794 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12794 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12794 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12794 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12794,cell12794,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12794 ⟨38,by decide⟩).lower ∧ (cell12794 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12794 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12794 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12794 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12794 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12794 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12794,cell12794,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12794 ⟨39,by decide⟩).lower ∧ (cell12794 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12794 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12794 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12794 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12794 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12794 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12794,cell12794,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12794 ⟨40,by decide⟩).lower ∧ (cell12794 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12794 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12794 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12794 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12794 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12794 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12794,cell12794,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12794 ⟨41,by decide⟩).lower ∧ (cell12794 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12794 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12794 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12794 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12794 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12794 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12794,cell12794,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12794 ⟨42,by decide⟩).lower ∧ (cell12794 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12794 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12794 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12794 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12794 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12794 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12794,cell12794,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12794 ⟨43,by decide⟩).lower ∧ (cell12794 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12794 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12794 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12794 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12794 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12794 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12794,cell12794,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12794 ⟨44,by decide⟩).lower ∧ (cell12794 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12794 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12794 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12794 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12794 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12794 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12794,cell12794,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12794 ⟨45,by decide⟩).lower ∧ (cell12794 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12794 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12794 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12794 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12794 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12794 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12794,cell12794,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12794 ⟨46,by decide⟩).lower ∧ (cell12794 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12794 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12794 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12794 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12794 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12794 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12794,cell12794,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12794 ⟨47,by decide⟩).lower ∧ (cell12794 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12794 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12794 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12794 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12794 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12794 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12794,cell12794,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12794 ⟨48,by decide⟩).lower ∧ (cell12794 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12794 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12794 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12794 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12794 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12794 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12794,cell12794,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12794 ⟨49,by decide⟩).lower ∧ (cell12794 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12794 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12794 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12794 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12794 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12794 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12794,cell12794,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12794 ⟨50,by decide⟩).lower ∧ (cell12794 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12794 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12794 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12794 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12794 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12794 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12794,cell12794,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12794 ⟨51,by decide⟩).lower ∧ (cell12794 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12794 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12794 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12794 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12794 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12794 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12794,cell12794,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12794 ⟨52,by decide⟩).lower ∧ (cell12794 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12794 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12794 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12794 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12794 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12794 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12794,cell12794,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12794 i).lower ∧
    (cell12794 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12794 i).upper ≤ (0.532 : ℝ) ∧
    (cell12794 i).centre ≤ (0.1 : ℝ) ∧ (cell12794 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12794 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12794 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12794

/-! The local source numeric instances at 12794 have no network premises. -/
namespace BstLean.Part269.N12794
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12794)
open BstLean.Part268 (cell12794)

noncomputable def sourceNumerics12794 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12794 (cell12794 i)
      scalarRow12794.M scalarRow12794.H scalarRow12794.xi := by
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
    energy_allowance := scalarRow12794.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12794]
    centre_nonneg := (scalarRow12794.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D17.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12794])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12794
/-! Actual 12795 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12795
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12795 ≤ (1.035674868541 : ℝ) := by
  have hr : (113.114985744595 : ℝ) ≤ √(12795 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.114985744595 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12795 12795 (11 / 1000) ≤
    (0.008450577928 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12795) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.114985744595 : ℝ) ≤ √(12795 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12795)
  have hdiv : K / √(12795 : ℝ) ≤ K / 113.114985744595 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.114985744595 ≤ (0.008450577928 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12795.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12795 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12795 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12795 := gPlus_lower 12795
end BstLean.Part269.N12795

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12795
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035674868540 : ℝ) ≤ wn 12795 := by
  have hn : √(12795 : ℝ) ≤ 113.114985744596 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12795 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.114985744596 ≤ 2 / √(12795 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000249978282 : ℝ) ≤ rhoBar 12795 BstLean.Part154.csC ∧
    rhoBar 12795 BstLean.Part154.csC ≤ 0.000249978669 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035674868540 : ℝ) / (1.295212 * 12795) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035674868541 : ℝ) / (1.29521 * 12795) := by gcongr
      _ ≤ (0.000249978669 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12795 BstLean.Part154.csC) ≤ 0.000999977166 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12795 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12795 BstLean.Part154.csC) (piBar (rhoBar 12795 BstLean.Part154.csC)) ≤ 0.000190935327 ∧
    cc1 (rhoBar 12795 BstLean.Part154.csC) (piBar (rhoBar 12795 BstLean.Part154.csC)) ≤ 0.000121493430 ∧
    cc2 (rhoBar 12795 BstLean.Part154.csC) ≤ 0.000070527884 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12795 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12795 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12795 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12795 BstLean.Part154.csC * nuR (rhoBar 12795 BstLean.Part154.csC)) ≤ 0.000499972961 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000249978669 : ℝ) * 0.000999977166 := by gcongr
      _ ≤ (0.000499972961 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12795 BstLean.Part154.csC) * nuR (rhoBar 12795 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000999977166 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12795 BstLean.Part154.csC) * rhoBar 12795 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000249978669 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000249978669 / 2 + 0.399 * 0.000999977166 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000190935327 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000499972961 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121493430 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000249978669 / 1.414213562 := by gcongr
      _ ≤ (0.000070527884 : ℝ) := by norm_num

end BstLean.Part269.N12795

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12795
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12795 BstLean.Part154.csC) (piBar (rhoBar 12795 BstLean.Part154.csC)) ≤ 1.57437E-7 := by
  have hr0 : 0 ≤ rhoBar 12795 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12795 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12795 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12795 BstLean.Part154.csC) (piBar (rhoBar 12795 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12795 BstLean.Part154.csC) (piBar (rhoBar 12795 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12795 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000190935327 : ℝ) ^ 2 + 0.000121493430 ^ 2 + 3 * 0.000070527884 ^ 2 +
        2 * 0.797885 * 0.000190935327 * 0.000121493430 + 2 * 0.000190935327 * 0.000070527884 +
        4 * 0.797885 * 0.000121493430 * 0.000070527884 := by gcongr
    _ ≤ (1.57437E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12795 BstLean.Part154.csC Θ ≤ 0.002609083365 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12795 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12795 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12795 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12795 BstLean.Part154.csC) (piBar (rhoBar 12795 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12795 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035674868541 * 1.57437E-7 / (0.000249978282 : ℝ) := by gcongr
    _ ≤ 0.002609083365 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12795 BstLean.Part154.csC Θ ≤ 0.002894549432 + 0.000659274980 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12795 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12795 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12795 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035674868541 : ℝ) * ((2 * Θ * 0.000249978669 +
        (6863 / 10000) * 0.000249978669 * 12795 * 0.000999977166) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002894549432 + 0.000659274980 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12795 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12795 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12795 0.011 Θ ∧ gammaRatio 12795 0.011 Θ ≤ 0.000085936202 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12795 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035674868541 : ℝ) * 0.525 / ((1 - 0.011) * 12795) := by gcongr
      _ ≤ (0.000085936202 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12795 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12795 0.011 Θ) :=
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
    badAllowance 12795 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000560204559 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12795 BstLean.Part154.csC) 1.22 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 2 (rhoBar 12795 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12795 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12795 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12795 0.011 Θ) 1.12 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 1 (gammaRatio 12795 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12795 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12795 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12795 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12795 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035674868541 : ℝ) * 12795 *
        (1.8602E-8 / 1.1045361 + 2.2721E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000560204559 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12795 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003454753991 + 0.003268358345 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12795

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12795
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12795 BstLean.Part154.csC) (piBar (rhoBar 12795 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12795 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12795 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12795 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12795 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12795 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12795 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12795 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12795 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12795 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12795 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12795 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12795 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12795 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12795 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052286998843 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12795) ≤ 0.010557730908 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12795 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035674868541)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010557730908 + 2 * 0.737676 / 12795) := by gcongr
    _ ≤ (0.052286998843 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12795 12 ≤ 0.0015 := by
  exact BstLean.Part269.S17.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12795

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12795
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560507832575 : ℝ) ≤ plow 12795 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12795) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052677242123)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001369768767) : eMP 12795 0.011 xi bn ≤ 0.001179377903 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12795 : ℝ) * (1 - 0.011))) ≤ 0.000583150026 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001369768767 / (12795 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000583150026 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000583150026 : ℝ) + 3.141593 * 0.052677242123 / (12795 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001179377903 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052677242123)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001369768767) : PiBarMP 12795 12 0.011 xi bn ≤ 0.160645368584 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12795 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037010387286 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.491132983893 : ℝ) ≤ √((12795 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.114985744595 : ℝ) ≤ √(12795 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12795) ≤ 0.123170313563 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037010387286 + 0.052677242123 * 1.772454 / (2 * (112.491132983893 : ℝ))) * (1 + 0.001179377903) +
        8 / (12795 * 113.114985744595) + 0.123170313563 := by gcongr
    _ ≤ (0.160645368584 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052677242123)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001369768767) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281802231721) :
    parallelOracle 12795 0.011 xi bn cd ≤ 0.161628642335 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12795 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12795 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560507832575 : ℝ) ≤ plow 12795 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.114985744595 : ℝ) ≤ √(12795 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281802231721 : ℝ) / (2 * 0.560507832575 * 113.114985744595)) * 0.160645368584 +
        0.281802231721 ^ 2 / (2 * 0.560507832575 * 113.114985744595) := by gcongr
    _ ≤ (0.161628642335 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052677242123) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001369768767)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281802231721) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12795 12795 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560507832575 : ℝ) ≤ plow 12795 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.114985744595 : ℝ) ≤ √(12795 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12795 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12795 Θ 1.22 ≤ 0.011723473166 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.114985744595 := by gcongr <;> linarith
      _ ≤ (0.011723473166 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12795 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12795 12795 0.011 ≤ 0.008450577928 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12795 12795 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12795 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12795 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12795 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12795 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161628642335 + 0.011723473166 + (0.008450577928 : ℝ) *
        (1 + 2 * (0.281802231721 + 0.011723473166) / (0.560507832575 * 113.114985744595))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12795]

end BstLean.Part269.N12795

/-! The original eight local profiles supply actual 12795 moment certificates. -/
namespace BstLean.Part269.N12795
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12795 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12795 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12795 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052677242123 ∧
    0 ≤ bN 12795 BstLean.Part154.csC (groupTheta g) ∧ bN 12795 BstLean.Part154.csC (groupTheta g) ≤ 0.001369768767 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12795 12795 0.011
      (momentAllowance 12795 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12795 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12795 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12795 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12795 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12795 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229515232878 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12795 0.011
      (momentAllowance 12795 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12795 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12795
/-! The actual computed-centre upper energy formula at 12795. -/
namespace BstLean.Part269.N12795
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12795

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12795
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12795)
open BstLean.Part268 (cell12795)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085217947321
  | 2 => 0.086155799394
  | 3 => 0.087091093884
  | 4 => 0.088025087048
  | 5 => 0.088959303540
  | 6 => 0.089895576932
  | 7 => 0.090836094170
  | 8 => 0.091783444037
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12795 12795 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12795 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003459522332 + 0.003273654356 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S17.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12795

/-! Actual upper energy certificates on all 43 source endpoints at 12795. -/
namespace BstLean.Part269.N12795
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12795)
open BstLean.Part268 (cell12795)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12795 (gMinus 12795) (1 - (cell12795 i).lower) ≤ 1 ∧
    energyUpper 12795 (gMinus 12795) (BstLean.Part211.gPlus 12795)
      (finiteEnergy 12795 12795 0.011) (1 - (cell12795 i).lower) ≤
      (cell12795 i).energy := by
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
      have E := BstLean.Part269.S17.uniformEnergy10 (n := 12795) (by norm_num)
        (q := 1 - (cell12795 ⟨10,by decide⟩).lower)
        (by norm_num [cell12795]) (by norm_num [cell12795])
      exact ⟨E.1,E.2.trans (by norm_num [cell12795])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy11 (n := 12795) (by norm_num)
        (q := 1 - (cell12795 ⟨11,by decide⟩).lower)
        (by norm_num [cell12795]) (by norm_num [cell12795])
      exact ⟨E.1,E.2.trans (by norm_num [cell12795])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy12 (n := 12795) (by norm_num)
        (q := 1 - (cell12795 ⟨12,by decide⟩).lower)
        (by norm_num [cell12795]) (by norm_num [cell12795])
      exact ⟨E.1,E.2.trans (by norm_num [cell12795])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy13 (n := 12795) (by norm_num)
        (q := 1 - (cell12795 ⟨13,by decide⟩).lower)
        (by norm_num [cell12795]) (by norm_num [cell12795])
      exact ⟨E.1,E.2.trans (by norm_num [cell12795])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy14 (n := 12795) (by norm_num)
        (q := 1 - (cell12795 ⟨14,by decide⟩).lower)
        (by norm_num [cell12795]) (by norm_num [cell12795])
      exact ⟨E.1,E.2.trans (by norm_num [cell12795])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy15 (n := 12795) (by norm_num)
        (q := 1 - (cell12795 ⟨15,by decide⟩).lower)
        (by norm_num [cell12795]) (by norm_num [cell12795])
      exact ⟨E.1,E.2.trans (by norm_num [cell12795])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy16 (n := 12795) (by norm_num)
        (q := 1 - (cell12795 ⟨16,by decide⟩).lower)
        (by norm_num [cell12795]) (by norm_num [cell12795])
      exact ⟨E.1,E.2.trans (by norm_num [cell12795])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy17 (n := 12795) (by norm_num)
        (q := 1 - (cell12795 ⟨17,by decide⟩).lower)
        (by norm_num [cell12795]) (by norm_num [cell12795])
      exact ⟨E.1,E.2.trans (by norm_num [cell12795])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy18 (n := 12795) (by norm_num)
        (q := 1 - (cell12795 ⟨18,by decide⟩).lower)
        (by norm_num [cell12795]) (by norm_num [cell12795])
      exact ⟨E.1,E.2.trans (by norm_num [cell12795])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy19 (n := 12795) (by norm_num)
        (q := 1 - (cell12795 ⟨19,by decide⟩).lower)
        (by norm_num [cell12795]) (by norm_num [cell12795])
      exact ⟨E.1,E.2.trans (by norm_num [cell12795])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy20 (n := 12795) (by norm_num)
        (q := 1 - (cell12795 ⟨20,by decide⟩).lower)
        (by norm_num [cell12795]) (by norm_num [cell12795])
      exact ⟨E.1,E.2.trans (by norm_num [cell12795])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy21 (n := 12795) (by norm_num)
        (q := 1 - (cell12795 ⟨21,by decide⟩).lower)
        (by norm_num [cell12795]) (by norm_num [cell12795])
      exact ⟨E.1,E.2.trans (by norm_num [cell12795])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy22 (n := 12795) (by norm_num)
        (q := 1 - (cell12795 ⟨22,by decide⟩).lower)
        (by norm_num [cell12795]) (by norm_num [cell12795])
      exact ⟨E.1,E.2.trans (by norm_num [cell12795])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy23 (n := 12795) (by norm_num)
        (q := 1 - (cell12795 ⟨23,by decide⟩).lower)
        (by norm_num [cell12795]) (by norm_num [cell12795])
      exact ⟨E.1,E.2.trans (by norm_num [cell12795])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy24 (n := 12795) (by norm_num)
        (q := 1 - (cell12795 ⟨24,by decide⟩).lower)
        (by norm_num [cell12795]) (by norm_num [cell12795])
      exact ⟨E.1,E.2.trans (by norm_num [cell12795])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy25 (n := 12795) (by norm_num)
        (q := 1 - (cell12795 ⟨25,by decide⟩).lower)
        (by norm_num [cell12795]) (by norm_num [cell12795])
      exact ⟨E.1,E.2.trans (by norm_num [cell12795])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy26 (n := 12795) (by norm_num)
        (q := 1 - (cell12795 ⟨26,by decide⟩).lower)
        (by norm_num [cell12795]) (by norm_num [cell12795])
      exact ⟨E.1,E.2.trans (by norm_num [cell12795])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy27 (n := 12795) (by norm_num)
        (q := 1 - (cell12795 ⟨27,by decide⟩).lower)
        (by norm_num [cell12795]) (by norm_num [cell12795])
      exact ⟨E.1,E.2.trans (by norm_num [cell12795])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy28 (n := 12795) (by norm_num)
        (q := 1 - (cell12795 ⟨28,by decide⟩).lower)
        (by norm_num [cell12795]) (by norm_num [cell12795])
      exact ⟨E.1,E.2.trans (by norm_num [cell12795])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy29 (n := 12795) (by norm_num)
        (q := 1 - (cell12795 ⟨29,by decide⟩).lower)
        (by norm_num [cell12795]) (by norm_num [cell12795])
      exact ⟨E.1,E.2.trans (by norm_num [cell12795])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy30 (n := 12795) (by norm_num)
        (q := 1 - (cell12795 ⟨30,by decide⟩).lower)
        (by norm_num [cell12795]) (by norm_num [cell12795])
      exact ⟨E.1,E.2.trans (by norm_num [cell12795])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy31 (n := 12795) (by norm_num)
        (q := 1 - (cell12795 ⟨31,by decide⟩).lower)
        (by norm_num [cell12795]) (by norm_num [cell12795])
      exact ⟨E.1,E.2.trans (by norm_num [cell12795])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy32 (n := 12795) (by norm_num)
        (q := 1 - (cell12795 ⟨32,by decide⟩).lower)
        (by norm_num [cell12795]) (by norm_num [cell12795])
      exact ⟨E.1,E.2.trans (by norm_num [cell12795])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy33 (n := 12795) (by norm_num)
        (q := 1 - (cell12795 ⟨33,by decide⟩).lower)
        (by norm_num [cell12795]) (by norm_num [cell12795])
      exact ⟨E.1,E.2.trans (by norm_num [cell12795])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy34 (n := 12795) (by norm_num)
        (q := 1 - (cell12795 ⟨34,by decide⟩).lower)
        (by norm_num [cell12795]) (by norm_num [cell12795])
      exact ⟨E.1,E.2.trans (by norm_num [cell12795])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy35 (n := 12795) (by norm_num)
        (q := 1 - (cell12795 ⟨35,by decide⟩).lower)
        (by norm_num [cell12795]) (by norm_num [cell12795])
      exact ⟨E.1,E.2.trans (by norm_num [cell12795])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy36 (n := 12795) (by norm_num)
        (q := 1 - (cell12795 ⟨36,by decide⟩).lower)
        (by norm_num [cell12795]) (by norm_num [cell12795])
      exact ⟨E.1,E.2.trans (by norm_num [cell12795])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy37 (n := 12795) (by norm_num)
        (q := 1 - (cell12795 ⟨37,by decide⟩).lower)
        (by norm_num [cell12795]) (by norm_num [cell12795])
      exact ⟨E.1,E.2.trans (by norm_num [cell12795])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy38 (n := 12795) (by norm_num)
        (q := 1 - (cell12795 ⟨38,by decide⟩).lower)
        (by norm_num [cell12795]) (by norm_num [cell12795])
      exact ⟨E.1,E.2.trans (by norm_num [cell12795])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy39 (n := 12795) (by norm_num)
        (q := 1 - (cell12795 ⟨39,by decide⟩).lower)
        (by norm_num [cell12795]) (by norm_num [cell12795])
      exact ⟨E.1,E.2.trans (by norm_num [cell12795])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy40 (n := 12795) (by norm_num)
        (q := 1 - (cell12795 ⟨40,by decide⟩).lower)
        (by norm_num [cell12795]) (by norm_num [cell12795])
      exact ⟨E.1,E.2.trans (by norm_num [cell12795])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy41 (n := 12795) (by norm_num)
        (q := 1 - (cell12795 ⟨41,by decide⟩).lower)
        (by norm_num [cell12795]) (by norm_num [cell12795])
      exact ⟨E.1,E.2.trans (by norm_num [cell12795])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy42 (n := 12795) (by norm_num)
        (q := 1 - (cell12795 ⟨42,by decide⟩).lower)
        (by norm_num [cell12795]) (by norm_num [cell12795])
      exact ⟨E.1,E.2.trans (by norm_num [cell12795])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy43 (n := 12795) (by norm_num)
        (q := 1 - (cell12795 ⟨43,by decide⟩).lower)
        (by norm_num [cell12795]) (by norm_num [cell12795])
      exact ⟨E.1,E.2.trans (by norm_num [cell12795])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy44 (n := 12795) (by norm_num)
        (q := 1 - (cell12795 ⟨44,by decide⟩).lower)
        (by norm_num [cell12795]) (by norm_num [cell12795])
      exact ⟨E.1,E.2.trans (by norm_num [cell12795])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy45 (n := 12795) (by norm_num)
        (q := 1 - (cell12795 ⟨45,by decide⟩).lower)
        (by norm_num [cell12795]) (by norm_num [cell12795])
      exact ⟨E.1,E.2.trans (by norm_num [cell12795])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy46 (n := 12795) (by norm_num)
        (q := 1 - (cell12795 ⟨46,by decide⟩).lower)
        (by norm_num [cell12795]) (by norm_num [cell12795])
      exact ⟨E.1,E.2.trans (by norm_num [cell12795])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy47 (n := 12795) (by norm_num)
        (q := 1 - (cell12795 ⟨47,by decide⟩).lower)
        (by norm_num [cell12795]) (by norm_num [cell12795])
      exact ⟨E.1,E.2.trans (by norm_num [cell12795])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy48 (n := 12795) (by norm_num)
        (q := 1 - (cell12795 ⟨48,by decide⟩).lower)
        (by norm_num [cell12795]) (by norm_num [cell12795])
      exact ⟨E.1,E.2.trans (by norm_num [cell12795])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy49 (n := 12795) (by norm_num)
        (q := 1 - (cell12795 ⟨49,by decide⟩).lower)
        (by norm_num [cell12795]) (by norm_num [cell12795])
      exact ⟨E.1,E.2.trans (by norm_num [cell12795])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy50 (n := 12795) (by norm_num)
        (q := 1 - (cell12795 ⟨50,by decide⟩).lower)
        (by norm_num [cell12795]) (by norm_num [cell12795])
      exact ⟨E.1,E.2.trans (by norm_num [cell12795])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy51 (n := 12795) (by norm_num)
        (q := 1 - (cell12795 ⟨51,by decide⟩).lower)
        (by norm_num [cell12795]) (by norm_num [cell12795])
      exact ⟨E.1,E.2.trans (by norm_num [cell12795])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy52 (n := 12795) (by norm_num)
        (q := 1 - (cell12795 ⟨52,by decide⟩).lower)
        (by norm_num [cell12795]) (by norm_num [cell12795])
      exact ⟨E.1,E.2.trans (by norm_num [cell12795])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12795

/-! Source-cell containment and simple scalar guards at 12795. -/
namespace BstLean.Part269.N12795
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12795)
open BstLean.Part268 (cell12795)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12795 ⟨10,by decide⟩).lower ∧ (cell12795 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12795 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12795 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12795 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12795 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12795 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12795,cell12795,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12795 ⟨11,by decide⟩).lower ∧ (cell12795 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12795 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12795 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12795 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12795 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12795 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12795,cell12795,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12795 ⟨12,by decide⟩).lower ∧ (cell12795 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12795 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12795 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12795 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12795 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12795 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12795,cell12795,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12795 ⟨13,by decide⟩).lower ∧ (cell12795 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12795 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12795 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12795 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12795 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12795 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12795,cell12795,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12795 ⟨14,by decide⟩).lower ∧ (cell12795 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12795 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12795 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12795 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12795 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12795 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12795,cell12795,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12795 ⟨15,by decide⟩).lower ∧ (cell12795 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12795 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12795 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12795 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12795 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12795 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12795,cell12795,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12795 ⟨16,by decide⟩).lower ∧ (cell12795 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12795 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12795 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12795 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12795 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12795 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12795,cell12795,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12795 ⟨17,by decide⟩).lower ∧ (cell12795 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12795 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12795 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12795 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12795 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12795 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12795,cell12795,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12795 ⟨18,by decide⟩).lower ∧ (cell12795 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12795 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12795 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12795 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12795 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12795 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12795,cell12795,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12795 ⟨19,by decide⟩).lower ∧ (cell12795 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12795 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12795 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12795 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12795 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12795 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12795,cell12795,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12795 ⟨20,by decide⟩).lower ∧ (cell12795 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12795 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12795 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12795 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12795 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12795 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12795,cell12795,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12795 ⟨21,by decide⟩).lower ∧ (cell12795 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12795 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12795 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12795 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12795 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12795 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12795,cell12795,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12795 ⟨22,by decide⟩).lower ∧ (cell12795 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12795 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12795 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12795 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12795 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12795 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12795,cell12795,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12795 ⟨23,by decide⟩).lower ∧ (cell12795 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12795 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12795 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12795 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12795 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12795 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12795,cell12795,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12795 ⟨24,by decide⟩).lower ∧ (cell12795 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12795 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12795 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12795 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12795 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12795 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12795,cell12795,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12795 ⟨25,by decide⟩).lower ∧ (cell12795 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12795 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12795 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12795 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12795 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12795 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12795,cell12795,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12795 ⟨26,by decide⟩).lower ∧ (cell12795 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12795 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12795 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12795 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12795 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12795 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12795,cell12795,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12795 ⟨27,by decide⟩).lower ∧ (cell12795 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12795 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12795 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12795 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12795 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12795 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12795,cell12795,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12795 ⟨28,by decide⟩).lower ∧ (cell12795 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12795 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12795 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12795 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12795 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12795 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12795,cell12795,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12795 ⟨29,by decide⟩).lower ∧ (cell12795 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12795 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12795 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12795 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12795 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12795 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12795,cell12795,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12795 ⟨30,by decide⟩).lower ∧ (cell12795 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12795 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12795 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12795 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12795 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12795 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12795,cell12795,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12795 ⟨31,by decide⟩).lower ∧ (cell12795 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12795 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12795 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12795 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12795 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12795 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12795,cell12795,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12795 ⟨32,by decide⟩).lower ∧ (cell12795 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12795 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12795 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12795 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12795 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12795 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12795,cell12795,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12795 ⟨33,by decide⟩).lower ∧ (cell12795 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12795 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12795 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12795 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12795 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12795 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12795,cell12795,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12795 ⟨34,by decide⟩).lower ∧ (cell12795 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12795 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12795 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12795 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12795 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12795 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12795,cell12795,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12795 ⟨35,by decide⟩).lower ∧ (cell12795 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12795 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12795 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12795 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12795 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12795 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12795,cell12795,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12795 ⟨36,by decide⟩).lower ∧ (cell12795 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12795 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12795 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12795 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12795 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12795 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12795,cell12795,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12795 ⟨37,by decide⟩).lower ∧ (cell12795 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12795 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12795 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12795 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12795 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12795 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12795,cell12795,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12795 ⟨38,by decide⟩).lower ∧ (cell12795 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12795 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12795 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12795 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12795 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12795 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12795,cell12795,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12795 ⟨39,by decide⟩).lower ∧ (cell12795 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12795 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12795 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12795 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12795 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12795 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12795,cell12795,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12795 ⟨40,by decide⟩).lower ∧ (cell12795 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12795 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12795 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12795 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12795 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12795 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12795,cell12795,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12795 ⟨41,by decide⟩).lower ∧ (cell12795 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12795 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12795 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12795 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12795 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12795 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12795,cell12795,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12795 ⟨42,by decide⟩).lower ∧ (cell12795 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12795 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12795 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12795 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12795 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12795 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12795,cell12795,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12795 ⟨43,by decide⟩).lower ∧ (cell12795 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12795 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12795 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12795 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12795 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12795 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12795,cell12795,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12795 ⟨44,by decide⟩).lower ∧ (cell12795 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12795 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12795 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12795 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12795 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12795 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12795,cell12795,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12795 ⟨45,by decide⟩).lower ∧ (cell12795 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12795 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12795 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12795 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12795 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12795 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12795,cell12795,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12795 ⟨46,by decide⟩).lower ∧ (cell12795 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12795 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12795 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12795 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12795 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12795 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12795,cell12795,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12795 ⟨47,by decide⟩).lower ∧ (cell12795 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12795 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12795 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12795 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12795 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12795 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12795,cell12795,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12795 ⟨48,by decide⟩).lower ∧ (cell12795 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12795 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12795 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12795 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12795 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12795 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12795,cell12795,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12795 ⟨49,by decide⟩).lower ∧ (cell12795 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12795 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12795 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12795 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12795 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12795 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12795,cell12795,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12795 ⟨50,by decide⟩).lower ∧ (cell12795 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12795 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12795 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12795 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12795 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12795 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12795,cell12795,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12795 ⟨51,by decide⟩).lower ∧ (cell12795 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12795 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12795 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12795 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12795 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12795 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12795,cell12795,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12795 ⟨52,by decide⟩).lower ∧ (cell12795 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12795 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12795 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12795 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12795 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12795 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12795,cell12795,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12795 i).lower ∧
    (cell12795 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12795 i).upper ≤ (0.532 : ℝ) ∧
    (cell12795 i).centre ≤ (0.1 : ℝ) ∧ (cell12795 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12795 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12795 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12795

/-! The local source numeric instances at 12795 have no network premises. -/
namespace BstLean.Part269.N12795
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12795)
open BstLean.Part268 (cell12795)

noncomputable def sourceNumerics12795 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12795 (cell12795 i)
      scalarRow12795.M scalarRow12795.H scalarRow12795.xi := by
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
    energy_allowance := scalarRow12795.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12795]
    centre_nonneg := (scalarRow12795.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D17.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12795])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12795
/-! Actual 12796 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12796
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12796 ≤ (1.035673462313 : ℝ) := by
  have hr : (113.119405939034 : ℝ) ≤ √(12796 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.119405939034 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12796 12796 (11 / 1000) ≤
    (0.008450247715 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12796) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.119405939034 : ℝ) ≤ √(12796 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12796)
  have hdiv : K / √(12796 : ℝ) ≤ K / 113.119405939034 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.119405939034 ≤ (0.008450247715 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12796.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12796 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12796 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12796 := gPlus_lower 12796
end BstLean.Part269.N12796

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12796
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035673462312 : ℝ) ≤ wn 12796 := by
  have hn : √(12796 : ℝ) ≤ 113.119405939035 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12796 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.119405939035 ≤ 2 / √(12796 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000249958407 : ℝ) ≤ rhoBar 12796 BstLean.Part154.csC ∧
    rhoBar 12796 BstLean.Part154.csC ≤ 0.000249958794 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035673462312 : ℝ) / (1.295212 * 12796) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035673462313 : ℝ) / (1.29521 * 12796) := by gcongr
      _ ≤ (0.000249958794 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12796 BstLean.Part154.csC) ≤ 0.000999897656 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12796 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12796 BstLean.Part154.csC) (piBar (rhoBar 12796 BstLean.Part154.csC)) ≤ 0.000190920145 ∧
    cc1 (rhoBar 12796 BstLean.Part154.csC) (piBar (rhoBar 12796 BstLean.Part154.csC)) ≤ 0.000121483770 ∧
    cc2 (rhoBar 12796 BstLean.Part154.csC) ≤ 0.000070522276 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12796 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12796 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12796 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12796 BstLean.Part154.csC * nuR (rhoBar 12796 BstLean.Part154.csC)) ≤ 0.000499933208 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000249958794 : ℝ) * 0.000999897656 := by gcongr
      _ ≤ (0.000499933208 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12796 BstLean.Part154.csC) * nuR (rhoBar 12796 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000999897656 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12796 BstLean.Part154.csC) * rhoBar 12796 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000249958794 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000249958794 / 2 + 0.399 * 0.000999897656 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000190920145 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000499933208 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121483770 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000249958794 / 1.414213562 := by gcongr
      _ ≤ (0.000070522276 : ℝ) := by norm_num

end BstLean.Part269.N12796

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12796
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12796 BstLean.Part154.csC) (piBar (rhoBar 12796 BstLean.Part154.csC)) ≤ 1.57412E-7 := by
  have hr0 : 0 ≤ rhoBar 12796 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12796 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12796 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12796 BstLean.Part154.csC) (piBar (rhoBar 12796 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12796 BstLean.Part154.csC) (piBar (rhoBar 12796 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12796 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000190920145 : ℝ) ^ 2 + 0.000121483770 ^ 2 + 3 * 0.000070522276 ^ 2 +
        2 * 0.797885 * 0.000190920145 * 0.000121483770 + 2 * 0.000190920145 * 0.000070522276 +
        4 * 0.797885 * 0.000121483770 * 0.000070522276 := by gcongr
    _ ≤ (1.57412E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12796 BstLean.Part154.csC Θ ≤ 0.002608872941 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12796 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12796 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12796 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12796 BstLean.Part154.csC) (piBar (rhoBar 12796 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12796 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035673462313 * 1.57412E-7 / (0.000249958407 : ℝ) := by gcongr
    _ ≤ 0.002608872941 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12796 BstLean.Part154.csC Θ ≤ 0.002894311422 + 0.000659221668 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12796 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12796 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12796 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035673462313 : ℝ) * ((2 * Θ * 0.000249958794 +
        (6863 / 10000) * 0.000249958794 * 12796 * 0.000999897656) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002894311422 + 0.000659221668 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12796 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12796 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12796 0.011 Θ ∧ gammaRatio 12796 0.011 Θ ≤ 0.000085929370 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12796 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035673462313 : ℝ) * 0.525 / ((1 - 0.011) * 12796) := by gcongr
      _ ≤ (0.000085929370 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12796 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12796 0.011 Θ) :=
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
    badAllowance 12796 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000560204559 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12796 BstLean.Part154.csC) 1.22 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 2 (rhoBar 12796 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12796 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12796 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12796 0.011 Θ) 1.12 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 1 (gammaRatio 12796 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12796 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12796 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12796 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12796 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035673462313 : ℝ) * 12796 *
        (1.8602E-8 / 1.1045361 + 2.2721E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000560204559 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12796 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003454515981 + 0.003268094609 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12796

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12796
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12796 BstLean.Part154.csC) (piBar (rhoBar 12796 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12796 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12796 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12796 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12796 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12796 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12796 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12796 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12796 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12796 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12796 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12796 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12796 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12796 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12796 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052284933628 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12796) ≤ 0.010557318359 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12796 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035673462313)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010557318359 + 2 * 0.737676 / 12796) := by gcongr
    _ ≤ (0.052284933628 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12796 12 ≤ 0.0015 := by
  exact BstLean.Part269.S17.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12796

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12796
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560507877125 : ℝ) ≤ plow 12796 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12796) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052676865651)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001369658295) : eMP 12796 0.011 xi bn ≤ 0.001179284184 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12796 : ℝ) * (1 - 0.011))) ≤ 0.000583103724 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001369658295 / (12796 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000583103724 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000583103724 : ℝ) + 3.141593 * 0.052676865651 / (12796 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001179284184 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052676865651)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001369658295) : PiBarMP 12796 12 0.011 xi bn ≤ 0.160639038048 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12796 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037008894810 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.495528800037 : ℝ) ≤ √((12796 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.119405939034 : ℝ) ≤ √(12796 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12796) ≤ 0.123165500624 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037008894810 + 0.052676865651 * 1.772454 / (2 * (112.495528800037 : ℝ))) * (1 + 0.001179284184) +
        8 / (12796 * 113.119405939034) + 0.123165500624 := by gcongr
    _ ≤ (0.160639038048 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052676865651)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001369658295) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281799346359) :
    parallelOracle 12796 0.011 xi bn cd ≤ 0.161622242752 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12796 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12796 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560507877125 : ℝ) ≤ plow 12796 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.119405939034 : ℝ) ≤ √(12796 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281799346359 : ℝ) / (2 * 0.560507877125 * 113.119405939034)) * 0.160639038048 +
        0.281799346359 ^ 2 / (2 * 0.560507877125 * 113.119405939034) := by gcongr
    _ ≤ (0.161622242752 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052676865651) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001369658295)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281799346359) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12796 12796 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560507877125 : ℝ) ≤ plow 12796 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.119405939034 : ℝ) ≤ √(12796 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12796 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12796 Θ 1.22 ≤ 0.011723015066 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.119405939034 := by gcongr <;> linarith
      _ ≤ (0.011723015066 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12796 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12796 12796 0.011 ≤ 0.008450247715 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12796 12796 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12796 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12796 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12796 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12796 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161622242752 + 0.011723015066 + (0.008450247715 : ℝ) *
        (1 + 2 * (0.281799346359 + 0.011723015066) / (0.560507877125 * 113.119405939034))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12796]

end BstLean.Part269.N12796

/-! The original eight local profiles supply actual 12796 moment certificates. -/
namespace BstLean.Part269.N12796
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12796 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12796 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12796 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052676865651 ∧
    0 ≤ bN 12796 BstLean.Part154.csC (groupTheta g) ∧ bN 12796 BstLean.Part154.csC (groupTheta g) ≤ 0.001369658295 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12796 12796 0.011
      (momentAllowance 12796 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12796 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12796 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12796 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12796 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12796 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229514412731 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12796 0.011
      (momentAllowance 12796 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12796 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12796
/-! The actual computed-centre upper energy formula at 12796. -/
namespace BstLean.Part269.N12796
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12796

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12796
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12796)
open BstLean.Part268 (cell12796)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085215129735
  | 2 => 0.086152932226
  | 3 => 0.087088170258
  | 4 => 0.088022098479
  | 5 => 0.088956239648
  | 6 => 0.089892425113
  | 7 => 0.090832839239
  | 8 => 0.091780067817
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12796 12796 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12796 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003459522332 + 0.003273654356 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S17.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12796

/-! Actual upper energy certificates on all 43 source endpoints at 12796. -/
namespace BstLean.Part269.N12796
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12796)
open BstLean.Part268 (cell12796)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12796 (gMinus 12796) (1 - (cell12796 i).lower) ≤ 1 ∧
    energyUpper 12796 (gMinus 12796) (BstLean.Part211.gPlus 12796)
      (finiteEnergy 12796 12796 0.011) (1 - (cell12796 i).lower) ≤
      (cell12796 i).energy := by
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
      have E := BstLean.Part269.S17.uniformEnergy10 (n := 12796) (by norm_num)
        (q := 1 - (cell12796 ⟨10,by decide⟩).lower)
        (by norm_num [cell12796]) (by norm_num [cell12796])
      exact ⟨E.1,E.2.trans (by norm_num [cell12796])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy11 (n := 12796) (by norm_num)
        (q := 1 - (cell12796 ⟨11,by decide⟩).lower)
        (by norm_num [cell12796]) (by norm_num [cell12796])
      exact ⟨E.1,E.2.trans (by norm_num [cell12796])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy12 (n := 12796) (by norm_num)
        (q := 1 - (cell12796 ⟨12,by decide⟩).lower)
        (by norm_num [cell12796]) (by norm_num [cell12796])
      exact ⟨E.1,E.2.trans (by norm_num [cell12796])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy13 (n := 12796) (by norm_num)
        (q := 1 - (cell12796 ⟨13,by decide⟩).lower)
        (by norm_num [cell12796]) (by norm_num [cell12796])
      exact ⟨E.1,E.2.trans (by norm_num [cell12796])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy14 (n := 12796) (by norm_num)
        (q := 1 - (cell12796 ⟨14,by decide⟩).lower)
        (by norm_num [cell12796]) (by norm_num [cell12796])
      exact ⟨E.1,E.2.trans (by norm_num [cell12796])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy15 (n := 12796) (by norm_num)
        (q := 1 - (cell12796 ⟨15,by decide⟩).lower)
        (by norm_num [cell12796]) (by norm_num [cell12796])
      exact ⟨E.1,E.2.trans (by norm_num [cell12796])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy16 (n := 12796) (by norm_num)
        (q := 1 - (cell12796 ⟨16,by decide⟩).lower)
        (by norm_num [cell12796]) (by norm_num [cell12796])
      exact ⟨E.1,E.2.trans (by norm_num [cell12796])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy17 (n := 12796) (by norm_num)
        (q := 1 - (cell12796 ⟨17,by decide⟩).lower)
        (by norm_num [cell12796]) (by norm_num [cell12796])
      exact ⟨E.1,E.2.trans (by norm_num [cell12796])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy18 (n := 12796) (by norm_num)
        (q := 1 - (cell12796 ⟨18,by decide⟩).lower)
        (by norm_num [cell12796]) (by norm_num [cell12796])
      exact ⟨E.1,E.2.trans (by norm_num [cell12796])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy19 (n := 12796) (by norm_num)
        (q := 1 - (cell12796 ⟨19,by decide⟩).lower)
        (by norm_num [cell12796]) (by norm_num [cell12796])
      exact ⟨E.1,E.2.trans (by norm_num [cell12796])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy20 (n := 12796) (by norm_num)
        (q := 1 - (cell12796 ⟨20,by decide⟩).lower)
        (by norm_num [cell12796]) (by norm_num [cell12796])
      exact ⟨E.1,E.2.trans (by norm_num [cell12796])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy21 (n := 12796) (by norm_num)
        (q := 1 - (cell12796 ⟨21,by decide⟩).lower)
        (by norm_num [cell12796]) (by norm_num [cell12796])
      exact ⟨E.1,E.2.trans (by norm_num [cell12796])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy22 (n := 12796) (by norm_num)
        (q := 1 - (cell12796 ⟨22,by decide⟩).lower)
        (by norm_num [cell12796]) (by norm_num [cell12796])
      exact ⟨E.1,E.2.trans (by norm_num [cell12796])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy23 (n := 12796) (by norm_num)
        (q := 1 - (cell12796 ⟨23,by decide⟩).lower)
        (by norm_num [cell12796]) (by norm_num [cell12796])
      exact ⟨E.1,E.2.trans (by norm_num [cell12796])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy24 (n := 12796) (by norm_num)
        (q := 1 - (cell12796 ⟨24,by decide⟩).lower)
        (by norm_num [cell12796]) (by norm_num [cell12796])
      exact ⟨E.1,E.2.trans (by norm_num [cell12796])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy25 (n := 12796) (by norm_num)
        (q := 1 - (cell12796 ⟨25,by decide⟩).lower)
        (by norm_num [cell12796]) (by norm_num [cell12796])
      exact ⟨E.1,E.2.trans (by norm_num [cell12796])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy26 (n := 12796) (by norm_num)
        (q := 1 - (cell12796 ⟨26,by decide⟩).lower)
        (by norm_num [cell12796]) (by norm_num [cell12796])
      exact ⟨E.1,E.2.trans (by norm_num [cell12796])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy27 (n := 12796) (by norm_num)
        (q := 1 - (cell12796 ⟨27,by decide⟩).lower)
        (by norm_num [cell12796]) (by norm_num [cell12796])
      exact ⟨E.1,E.2.trans (by norm_num [cell12796])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy28 (n := 12796) (by norm_num)
        (q := 1 - (cell12796 ⟨28,by decide⟩).lower)
        (by norm_num [cell12796]) (by norm_num [cell12796])
      exact ⟨E.1,E.2.trans (by norm_num [cell12796])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy29 (n := 12796) (by norm_num)
        (q := 1 - (cell12796 ⟨29,by decide⟩).lower)
        (by norm_num [cell12796]) (by norm_num [cell12796])
      exact ⟨E.1,E.2.trans (by norm_num [cell12796])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy30 (n := 12796) (by norm_num)
        (q := 1 - (cell12796 ⟨30,by decide⟩).lower)
        (by norm_num [cell12796]) (by norm_num [cell12796])
      exact ⟨E.1,E.2.trans (by norm_num [cell12796])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy31 (n := 12796) (by norm_num)
        (q := 1 - (cell12796 ⟨31,by decide⟩).lower)
        (by norm_num [cell12796]) (by norm_num [cell12796])
      exact ⟨E.1,E.2.trans (by norm_num [cell12796])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy32 (n := 12796) (by norm_num)
        (q := 1 - (cell12796 ⟨32,by decide⟩).lower)
        (by norm_num [cell12796]) (by norm_num [cell12796])
      exact ⟨E.1,E.2.trans (by norm_num [cell12796])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy33 (n := 12796) (by norm_num)
        (q := 1 - (cell12796 ⟨33,by decide⟩).lower)
        (by norm_num [cell12796]) (by norm_num [cell12796])
      exact ⟨E.1,E.2.trans (by norm_num [cell12796])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy34 (n := 12796) (by norm_num)
        (q := 1 - (cell12796 ⟨34,by decide⟩).lower)
        (by norm_num [cell12796]) (by norm_num [cell12796])
      exact ⟨E.1,E.2.trans (by norm_num [cell12796])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy35 (n := 12796) (by norm_num)
        (q := 1 - (cell12796 ⟨35,by decide⟩).lower)
        (by norm_num [cell12796]) (by norm_num [cell12796])
      exact ⟨E.1,E.2.trans (by norm_num [cell12796])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy36 (n := 12796) (by norm_num)
        (q := 1 - (cell12796 ⟨36,by decide⟩).lower)
        (by norm_num [cell12796]) (by norm_num [cell12796])
      exact ⟨E.1,E.2.trans (by norm_num [cell12796])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy37 (n := 12796) (by norm_num)
        (q := 1 - (cell12796 ⟨37,by decide⟩).lower)
        (by norm_num [cell12796]) (by norm_num [cell12796])
      exact ⟨E.1,E.2.trans (by norm_num [cell12796])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy38 (n := 12796) (by norm_num)
        (q := 1 - (cell12796 ⟨38,by decide⟩).lower)
        (by norm_num [cell12796]) (by norm_num [cell12796])
      exact ⟨E.1,E.2.trans (by norm_num [cell12796])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy39 (n := 12796) (by norm_num)
        (q := 1 - (cell12796 ⟨39,by decide⟩).lower)
        (by norm_num [cell12796]) (by norm_num [cell12796])
      exact ⟨E.1,E.2.trans (by norm_num [cell12796])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy40 (n := 12796) (by norm_num)
        (q := 1 - (cell12796 ⟨40,by decide⟩).lower)
        (by norm_num [cell12796]) (by norm_num [cell12796])
      exact ⟨E.1,E.2.trans (by norm_num [cell12796])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy41 (n := 12796) (by norm_num)
        (q := 1 - (cell12796 ⟨41,by decide⟩).lower)
        (by norm_num [cell12796]) (by norm_num [cell12796])
      exact ⟨E.1,E.2.trans (by norm_num [cell12796])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy42 (n := 12796) (by norm_num)
        (q := 1 - (cell12796 ⟨42,by decide⟩).lower)
        (by norm_num [cell12796]) (by norm_num [cell12796])
      exact ⟨E.1,E.2.trans (by norm_num [cell12796])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy43 (n := 12796) (by norm_num)
        (q := 1 - (cell12796 ⟨43,by decide⟩).lower)
        (by norm_num [cell12796]) (by norm_num [cell12796])
      exact ⟨E.1,E.2.trans (by norm_num [cell12796])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy44 (n := 12796) (by norm_num)
        (q := 1 - (cell12796 ⟨44,by decide⟩).lower)
        (by norm_num [cell12796]) (by norm_num [cell12796])
      exact ⟨E.1,E.2.trans (by norm_num [cell12796])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy45 (n := 12796) (by norm_num)
        (q := 1 - (cell12796 ⟨45,by decide⟩).lower)
        (by norm_num [cell12796]) (by norm_num [cell12796])
      exact ⟨E.1,E.2.trans (by norm_num [cell12796])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy46 (n := 12796) (by norm_num)
        (q := 1 - (cell12796 ⟨46,by decide⟩).lower)
        (by norm_num [cell12796]) (by norm_num [cell12796])
      exact ⟨E.1,E.2.trans (by norm_num [cell12796])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy47 (n := 12796) (by norm_num)
        (q := 1 - (cell12796 ⟨47,by decide⟩).lower)
        (by norm_num [cell12796]) (by norm_num [cell12796])
      exact ⟨E.1,E.2.trans (by norm_num [cell12796])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy48 (n := 12796) (by norm_num)
        (q := 1 - (cell12796 ⟨48,by decide⟩).lower)
        (by norm_num [cell12796]) (by norm_num [cell12796])
      exact ⟨E.1,E.2.trans (by norm_num [cell12796])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy49 (n := 12796) (by norm_num)
        (q := 1 - (cell12796 ⟨49,by decide⟩).lower)
        (by norm_num [cell12796]) (by norm_num [cell12796])
      exact ⟨E.1,E.2.trans (by norm_num [cell12796])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy50 (n := 12796) (by norm_num)
        (q := 1 - (cell12796 ⟨50,by decide⟩).lower)
        (by norm_num [cell12796]) (by norm_num [cell12796])
      exact ⟨E.1,E.2.trans (by norm_num [cell12796])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy51 (n := 12796) (by norm_num)
        (q := 1 - (cell12796 ⟨51,by decide⟩).lower)
        (by norm_num [cell12796]) (by norm_num [cell12796])
      exact ⟨E.1,E.2.trans (by norm_num [cell12796])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy52 (n := 12796) (by norm_num)
        (q := 1 - (cell12796 ⟨52,by decide⟩).lower)
        (by norm_num [cell12796]) (by norm_num [cell12796])
      exact ⟨E.1,E.2.trans (by norm_num [cell12796])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12796

/-! Source-cell containment and simple scalar guards at 12796. -/
namespace BstLean.Part269.N12796
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12796)
open BstLean.Part268 (cell12796)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12796 ⟨10,by decide⟩).lower ∧ (cell12796 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12796 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12796 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12796 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12796 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12796 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12796,cell12796,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12796 ⟨11,by decide⟩).lower ∧ (cell12796 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12796 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12796 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12796 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12796 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12796 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12796,cell12796,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12796 ⟨12,by decide⟩).lower ∧ (cell12796 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12796 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12796 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12796 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12796 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12796 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12796,cell12796,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12796 ⟨13,by decide⟩).lower ∧ (cell12796 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12796 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12796 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12796 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12796 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12796 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12796,cell12796,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12796 ⟨14,by decide⟩).lower ∧ (cell12796 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12796 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12796 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12796 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12796 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12796 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12796,cell12796,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12796 ⟨15,by decide⟩).lower ∧ (cell12796 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12796 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12796 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12796 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12796 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12796 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12796,cell12796,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12796 ⟨16,by decide⟩).lower ∧ (cell12796 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12796 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12796 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12796 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12796 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12796 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12796,cell12796,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12796 ⟨17,by decide⟩).lower ∧ (cell12796 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12796 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12796 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12796 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12796 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12796 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12796,cell12796,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12796 ⟨18,by decide⟩).lower ∧ (cell12796 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12796 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12796 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12796 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12796 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12796 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12796,cell12796,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12796 ⟨19,by decide⟩).lower ∧ (cell12796 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12796 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12796 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12796 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12796 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12796 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12796,cell12796,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12796 ⟨20,by decide⟩).lower ∧ (cell12796 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12796 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12796 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12796 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12796 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12796 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12796,cell12796,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12796 ⟨21,by decide⟩).lower ∧ (cell12796 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12796 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12796 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12796 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12796 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12796 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12796,cell12796,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12796 ⟨22,by decide⟩).lower ∧ (cell12796 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12796 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12796 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12796 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12796 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12796 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12796,cell12796,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12796 ⟨23,by decide⟩).lower ∧ (cell12796 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12796 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12796 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12796 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12796 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12796 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12796,cell12796,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12796 ⟨24,by decide⟩).lower ∧ (cell12796 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12796 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12796 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12796 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12796 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12796 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12796,cell12796,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12796 ⟨25,by decide⟩).lower ∧ (cell12796 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12796 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12796 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12796 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12796 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12796 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12796,cell12796,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12796 ⟨26,by decide⟩).lower ∧ (cell12796 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12796 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12796 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12796 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12796 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12796 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12796,cell12796,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12796 ⟨27,by decide⟩).lower ∧ (cell12796 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12796 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12796 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12796 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12796 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12796 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12796,cell12796,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12796 ⟨28,by decide⟩).lower ∧ (cell12796 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12796 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12796 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12796 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12796 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12796 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12796,cell12796,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12796 ⟨29,by decide⟩).lower ∧ (cell12796 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12796 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12796 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12796 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12796 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12796 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12796,cell12796,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12796 ⟨30,by decide⟩).lower ∧ (cell12796 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12796 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12796 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12796 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12796 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12796 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12796,cell12796,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12796 ⟨31,by decide⟩).lower ∧ (cell12796 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12796 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12796 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12796 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12796 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12796 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12796,cell12796,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12796 ⟨32,by decide⟩).lower ∧ (cell12796 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12796 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12796 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12796 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12796 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12796 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12796,cell12796,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12796 ⟨33,by decide⟩).lower ∧ (cell12796 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12796 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12796 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12796 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12796 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12796 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12796,cell12796,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12796 ⟨34,by decide⟩).lower ∧ (cell12796 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12796 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12796 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12796 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12796 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12796 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12796,cell12796,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12796 ⟨35,by decide⟩).lower ∧ (cell12796 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12796 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12796 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12796 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12796 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12796 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12796,cell12796,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12796 ⟨36,by decide⟩).lower ∧ (cell12796 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12796 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12796 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12796 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12796 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12796 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12796,cell12796,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12796 ⟨37,by decide⟩).lower ∧ (cell12796 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12796 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12796 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12796 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12796 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12796 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12796,cell12796,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12796 ⟨38,by decide⟩).lower ∧ (cell12796 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12796 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12796 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12796 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12796 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12796 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12796,cell12796,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12796 ⟨39,by decide⟩).lower ∧ (cell12796 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12796 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12796 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12796 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12796 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12796 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12796,cell12796,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12796 ⟨40,by decide⟩).lower ∧ (cell12796 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12796 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12796 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12796 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12796 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12796 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12796,cell12796,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12796 ⟨41,by decide⟩).lower ∧ (cell12796 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12796 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12796 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12796 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12796 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12796 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12796,cell12796,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12796 ⟨42,by decide⟩).lower ∧ (cell12796 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12796 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12796 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12796 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12796 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12796 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12796,cell12796,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12796 ⟨43,by decide⟩).lower ∧ (cell12796 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12796 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12796 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12796 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12796 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12796 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12796,cell12796,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12796 ⟨44,by decide⟩).lower ∧ (cell12796 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12796 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12796 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12796 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12796 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12796 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12796,cell12796,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12796 ⟨45,by decide⟩).lower ∧ (cell12796 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12796 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12796 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12796 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12796 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12796 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12796,cell12796,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12796 ⟨46,by decide⟩).lower ∧ (cell12796 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12796 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12796 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12796 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12796 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12796 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12796,cell12796,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12796 ⟨47,by decide⟩).lower ∧ (cell12796 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12796 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12796 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12796 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12796 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12796 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12796,cell12796,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12796 ⟨48,by decide⟩).lower ∧ (cell12796 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12796 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12796 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12796 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12796 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12796 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12796,cell12796,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12796 ⟨49,by decide⟩).lower ∧ (cell12796 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12796 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12796 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12796 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12796 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12796 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12796,cell12796,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12796 ⟨50,by decide⟩).lower ∧ (cell12796 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12796 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12796 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12796 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12796 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12796 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12796,cell12796,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12796 ⟨51,by decide⟩).lower ∧ (cell12796 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12796 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12796 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12796 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12796 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12796 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12796,cell12796,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12796 ⟨52,by decide⟩).lower ∧ (cell12796 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12796 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12796 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12796 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12796 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12796 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12796,cell12796,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12796 i).lower ∧
    (cell12796 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12796 i).upper ≤ (0.532 : ℝ) ∧
    (cell12796 i).centre ≤ (0.1 : ℝ) ∧ (cell12796 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12796 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12796 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12796

/-! The local source numeric instances at 12796 have no network premises. -/
namespace BstLean.Part269.N12796
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12796)
open BstLean.Part268 (cell12796)

noncomputable def sourceNumerics12796 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12796 (cell12796 i)
      scalarRow12796.M scalarRow12796.H scalarRow12796.xi := by
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
    energy_allowance := scalarRow12796.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12796]
    centre_nonneg := (scalarRow12796.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D17.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12796])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12796
/-! Actual 12797 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12797
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12797 ≤ (1.035672056251 : ℝ) := by
  have hr : (113.123825960758 : ℝ) ≤ √(12797 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.123825960758 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12797 12797 (11 / 1000) ≤
    (0.008449917541 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12797) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.123825960758 : ℝ) ≤ √(12797 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12797)
  have hdiv : K / √(12797 : ℝ) ≤ K / 113.123825960758 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.123825960758 ≤ (0.008449917541 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12797.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12797 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12797 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12797 := gPlus_lower 12797
end BstLean.Part269.N12797

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12797
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035672056250 : ℝ) ≤ wn 12797 := by
  have hn : √(12797 : ℝ) ≤ 113.123825960759 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12797 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.123825960759 ≤ 2 / √(12797 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000249938535 : ℝ) ≤ rhoBar 12797 BstLean.Part154.csC ∧
    rhoBar 12797 BstLean.Part154.csC ≤ 0.000249938922 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035672056250 : ℝ) / (1.295212 * 12797) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035672056251 : ℝ) / (1.29521 * 12797) := by gcongr
      _ ≤ (0.000249938922 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12797 BstLean.Part154.csC) ≤ 0.000999818158 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12797 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12797 BstLean.Part154.csC) (piBar (rhoBar 12797 BstLean.Part154.csC)) ≤ 0.000190904966 ∧
    cc1 (rhoBar 12797 BstLean.Part154.csC) (piBar (rhoBar 12797 BstLean.Part154.csC)) ≤ 0.000121474112 ∧
    cc2 (rhoBar 12797 BstLean.Part154.csC) ≤ 0.000070516670 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12797 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12797 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12797 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12797 BstLean.Part154.csC * nuR (rhoBar 12797 BstLean.Part154.csC)) ≤ 0.000499893462 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000249938922 : ℝ) * 0.000999818158 := by gcongr
      _ ≤ (0.000499893462 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12797 BstLean.Part154.csC) * nuR (rhoBar 12797 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000999818158 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12797 BstLean.Part154.csC) * rhoBar 12797 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000249938922 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000249938922 / 2 + 0.399 * 0.000999818158 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000190904966 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000499893462 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121474112 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000249938922 / 1.414213562 := by gcongr
      _ ≤ (0.000070516670 : ℝ) := by norm_num

end BstLean.Part269.N12797

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12797
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12797 BstLean.Part154.csC) (piBar (rhoBar 12797 BstLean.Part154.csC)) ≤ 1.57387E-7 := by
  have hr0 : 0 ≤ rhoBar 12797 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12797 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12797 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12797 BstLean.Part154.csC) (piBar (rhoBar 12797 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12797 BstLean.Part154.csC) (piBar (rhoBar 12797 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12797 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000190904966 : ℝ) ^ 2 + 0.000121474112 ^ 2 + 3 * 0.000070516670 ^ 2 +
        2 * 0.797885 * 0.000190904966 * 0.000121474112 + 2 * 0.000190904966 * 0.000070516670 +
        4 * 0.797885 * 0.000121474112 * 0.000070516670 := by gcongr
    _ ≤ (1.57387E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12797 BstLean.Part154.csC Θ ≤ 0.002608662453 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12797 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12797 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12797 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12797 BstLean.Part154.csC) (piBar (rhoBar 12797 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12797 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035672056251 * 1.57387E-7 / (0.000249938535 : ℝ) := by gcongr
    _ ≤ 0.002608662453 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12797 BstLean.Part154.csC Θ ≤ 0.002894073447 + 0.000659168364 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12797 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12797 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12797 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035672056251 : ℝ) * ((2 * Θ * 0.000249938922 +
        (6863 / 10000) * 0.000249938922 * 12797 * 0.000999818158) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002894073447 + 0.000659168364 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12797 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12797 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12797 0.011 Θ ∧ gammaRatio 12797 0.011 Θ ≤ 0.000085922538 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12797 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035672056251 : ℝ) * 0.525 / ((1 - 0.011) * 12797) := by gcongr
      _ ≤ (0.000085922538 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12797 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12797 0.011 Θ) :=
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
    badAllowance 12797 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000560204559 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12797 BstLean.Part154.csC) 1.22 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 2 (rhoBar 12797 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12797 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12797 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12797 0.011 Θ) 1.12 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 1 (gammaRatio 12797 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12797 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12797 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12797 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12797 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035672056251 : ℝ) * 12797 *
        (1.8602E-8 / 1.1045361 + 2.2721E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000560204559 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12797 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003454278006 + 0.003267830817 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12797

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12797
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12797 BstLean.Part154.csC) (piBar (rhoBar 12797 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12797 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12797 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12797 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12797 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12797 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12797 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12797 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12797 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12797 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12797 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12797 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12797 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12797 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12797 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052282868661 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12797) ≤ 0.010556905859 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12797 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035672056251)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010556905859 + 2 * 0.737676 / 12797) := by gcongr
    _ ≤ (0.052282868661 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12797 12 ≤ 0.0015 := by
  exact BstLean.Part269.S17.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12797

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12797
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560507921669 : ℝ) ≤ plow 12797 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12797) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052676489185)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001369547788) : eMP 12797 0.011 xi bn ≤ 0.001179190456 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12797 : ℝ) * (1 - 0.011))) ≤ 0.000583057418 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001369547788 / (12797 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000583057418 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000583057418 : ℝ) + 3.141593 * 0.052676489185 / (12797 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001179190456 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052676489185)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001369547788) : PiBarMP 12797 12 0.011 xi bn ≤ 0.160632707547 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12797 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037007401801 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.499924444419 : ℝ) ≤ √((12797 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.123825960758 : ℝ) ≤ √(12797 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12797) ≤ 0.123160688250 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037007401801 + 0.052676489185 * 1.772454 / (2 * (112.499924444419 : ℝ))) * (1 + 0.001179190456) +
        8 / (12797 * 113.123825960758) + 0.123160688250 := by gcongr
    _ ≤ (0.160632707547 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052676489185)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001369547788) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281796461255) :
    parallelOracle 12797 0.011 xi bn cd ≤ 0.161615843213 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12797 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12797 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560507921669 : ℝ) ≤ plow 12797 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.123825960758 : ℝ) ≤ √(12797 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281796461255 : ℝ) / (2 * 0.560507921669 * 113.123825960758)) * 0.160632707547 +
        0.281796461255 ^ 2 / (2 * 0.560507921669 * 113.123825960758) := by gcongr
    _ ≤ (0.161615843213 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052676489185) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001369547788)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281796461255) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12797 12797 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560507921669 : ℝ) ≤ plow 12797 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.123825960758 : ℝ) ≤ √(12797 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12797 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12797 Θ 1.22 ≤ 0.011722557019 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.123825960758 := by gcongr <;> linarith
      _ ≤ (0.011722557019 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12797 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12797 12797 0.011 ≤ 0.008449917541 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12797 12797 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12797 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12797 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12797 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12797 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161615843213 + 0.011722557019 + (0.008449917541 : ℝ) *
        (1 + 2 * (0.281796461255 + 0.011722557019) / (0.560507921669 * 113.123825960758))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12797]

end BstLean.Part269.N12797

/-! The original eight local profiles supply actual 12797 moment certificates. -/
namespace BstLean.Part269.N12797
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12797 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12797 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12797 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052676489185 ∧
    0 ≤ bN 12797 BstLean.Part154.csC (groupTheta g) ∧ bN 12797 BstLean.Part154.csC (groupTheta g) ≤ 0.001369547788 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12797 12797 0.011
      (momentAllowance 12797 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12797 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12797 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12797 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12797 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12797 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229513592594 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12797 0.011
      (momentAllowance 12797 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12797 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12797
/-! The actual computed-centre upper energy formula at 12797. -/
namespace BstLean.Part269.N12797
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12797

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12797
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12797)
open BstLean.Part268 (cell12797)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085212313134
  | 2 => 0.086150066083
  | 3 => 0.087085247705
  | 4 => 0.088019111043
  | 5 => 0.088953176960
  | 6 => 0.089889274588
  | 7 => 0.090829585709
  | 8 => 0.091776693130
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12797 12797 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12797 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003459522332 + 0.003273654356 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S17.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12797

/-! Actual upper energy certificates on all 43 source endpoints at 12797. -/
namespace BstLean.Part269.N12797
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12797)
open BstLean.Part268 (cell12797)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12797 (gMinus 12797) (1 - (cell12797 i).lower) ≤ 1 ∧
    energyUpper 12797 (gMinus 12797) (BstLean.Part211.gPlus 12797)
      (finiteEnergy 12797 12797 0.011) (1 - (cell12797 i).lower) ≤
      (cell12797 i).energy := by
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
      have E := BstLean.Part269.S17.uniformEnergy10 (n := 12797) (by norm_num)
        (q := 1 - (cell12797 ⟨10,by decide⟩).lower)
        (by norm_num [cell12797]) (by norm_num [cell12797])
      exact ⟨E.1,E.2.trans (by norm_num [cell12797])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy11 (n := 12797) (by norm_num)
        (q := 1 - (cell12797 ⟨11,by decide⟩).lower)
        (by norm_num [cell12797]) (by norm_num [cell12797])
      exact ⟨E.1,E.2.trans (by norm_num [cell12797])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy12 (n := 12797) (by norm_num)
        (q := 1 - (cell12797 ⟨12,by decide⟩).lower)
        (by norm_num [cell12797]) (by norm_num [cell12797])
      exact ⟨E.1,E.2.trans (by norm_num [cell12797])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy13 (n := 12797) (by norm_num)
        (q := 1 - (cell12797 ⟨13,by decide⟩).lower)
        (by norm_num [cell12797]) (by norm_num [cell12797])
      exact ⟨E.1,E.2.trans (by norm_num [cell12797])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy14 (n := 12797) (by norm_num)
        (q := 1 - (cell12797 ⟨14,by decide⟩).lower)
        (by norm_num [cell12797]) (by norm_num [cell12797])
      exact ⟨E.1,E.2.trans (by norm_num [cell12797])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy15 (n := 12797) (by norm_num)
        (q := 1 - (cell12797 ⟨15,by decide⟩).lower)
        (by norm_num [cell12797]) (by norm_num [cell12797])
      exact ⟨E.1,E.2.trans (by norm_num [cell12797])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy16 (n := 12797) (by norm_num)
        (q := 1 - (cell12797 ⟨16,by decide⟩).lower)
        (by norm_num [cell12797]) (by norm_num [cell12797])
      exact ⟨E.1,E.2.trans (by norm_num [cell12797])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy17 (n := 12797) (by norm_num)
        (q := 1 - (cell12797 ⟨17,by decide⟩).lower)
        (by norm_num [cell12797]) (by norm_num [cell12797])
      exact ⟨E.1,E.2.trans (by norm_num [cell12797])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy18 (n := 12797) (by norm_num)
        (q := 1 - (cell12797 ⟨18,by decide⟩).lower)
        (by norm_num [cell12797]) (by norm_num [cell12797])
      exact ⟨E.1,E.2.trans (by norm_num [cell12797])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy19 (n := 12797) (by norm_num)
        (q := 1 - (cell12797 ⟨19,by decide⟩).lower)
        (by norm_num [cell12797]) (by norm_num [cell12797])
      exact ⟨E.1,E.2.trans (by norm_num [cell12797])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy20 (n := 12797) (by norm_num)
        (q := 1 - (cell12797 ⟨20,by decide⟩).lower)
        (by norm_num [cell12797]) (by norm_num [cell12797])
      exact ⟨E.1,E.2.trans (by norm_num [cell12797])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy21 (n := 12797) (by norm_num)
        (q := 1 - (cell12797 ⟨21,by decide⟩).lower)
        (by norm_num [cell12797]) (by norm_num [cell12797])
      exact ⟨E.1,E.2.trans (by norm_num [cell12797])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy22 (n := 12797) (by norm_num)
        (q := 1 - (cell12797 ⟨22,by decide⟩).lower)
        (by norm_num [cell12797]) (by norm_num [cell12797])
      exact ⟨E.1,E.2.trans (by norm_num [cell12797])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy23 (n := 12797) (by norm_num)
        (q := 1 - (cell12797 ⟨23,by decide⟩).lower)
        (by norm_num [cell12797]) (by norm_num [cell12797])
      exact ⟨E.1,E.2.trans (by norm_num [cell12797])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy24 (n := 12797) (by norm_num)
        (q := 1 - (cell12797 ⟨24,by decide⟩).lower)
        (by norm_num [cell12797]) (by norm_num [cell12797])
      exact ⟨E.1,E.2.trans (by norm_num [cell12797])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy25 (n := 12797) (by norm_num)
        (q := 1 - (cell12797 ⟨25,by decide⟩).lower)
        (by norm_num [cell12797]) (by norm_num [cell12797])
      exact ⟨E.1,E.2.trans (by norm_num [cell12797])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy26 (n := 12797) (by norm_num)
        (q := 1 - (cell12797 ⟨26,by decide⟩).lower)
        (by norm_num [cell12797]) (by norm_num [cell12797])
      exact ⟨E.1,E.2.trans (by norm_num [cell12797])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy27 (n := 12797) (by norm_num)
        (q := 1 - (cell12797 ⟨27,by decide⟩).lower)
        (by norm_num [cell12797]) (by norm_num [cell12797])
      exact ⟨E.1,E.2.trans (by norm_num [cell12797])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy28 (n := 12797) (by norm_num)
        (q := 1 - (cell12797 ⟨28,by decide⟩).lower)
        (by norm_num [cell12797]) (by norm_num [cell12797])
      exact ⟨E.1,E.2.trans (by norm_num [cell12797])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy29 (n := 12797) (by norm_num)
        (q := 1 - (cell12797 ⟨29,by decide⟩).lower)
        (by norm_num [cell12797]) (by norm_num [cell12797])
      exact ⟨E.1,E.2.trans (by norm_num [cell12797])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy30 (n := 12797) (by norm_num)
        (q := 1 - (cell12797 ⟨30,by decide⟩).lower)
        (by norm_num [cell12797]) (by norm_num [cell12797])
      exact ⟨E.1,E.2.trans (by norm_num [cell12797])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy31 (n := 12797) (by norm_num)
        (q := 1 - (cell12797 ⟨31,by decide⟩).lower)
        (by norm_num [cell12797]) (by norm_num [cell12797])
      exact ⟨E.1,E.2.trans (by norm_num [cell12797])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy32 (n := 12797) (by norm_num)
        (q := 1 - (cell12797 ⟨32,by decide⟩).lower)
        (by norm_num [cell12797]) (by norm_num [cell12797])
      exact ⟨E.1,E.2.trans (by norm_num [cell12797])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy33 (n := 12797) (by norm_num)
        (q := 1 - (cell12797 ⟨33,by decide⟩).lower)
        (by norm_num [cell12797]) (by norm_num [cell12797])
      exact ⟨E.1,E.2.trans (by norm_num [cell12797])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy34 (n := 12797) (by norm_num)
        (q := 1 - (cell12797 ⟨34,by decide⟩).lower)
        (by norm_num [cell12797]) (by norm_num [cell12797])
      exact ⟨E.1,E.2.trans (by norm_num [cell12797])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy35 (n := 12797) (by norm_num)
        (q := 1 - (cell12797 ⟨35,by decide⟩).lower)
        (by norm_num [cell12797]) (by norm_num [cell12797])
      exact ⟨E.1,E.2.trans (by norm_num [cell12797])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy36 (n := 12797) (by norm_num)
        (q := 1 - (cell12797 ⟨36,by decide⟩).lower)
        (by norm_num [cell12797]) (by norm_num [cell12797])
      exact ⟨E.1,E.2.trans (by norm_num [cell12797])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy37 (n := 12797) (by norm_num)
        (q := 1 - (cell12797 ⟨37,by decide⟩).lower)
        (by norm_num [cell12797]) (by norm_num [cell12797])
      exact ⟨E.1,E.2.trans (by norm_num [cell12797])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy38 (n := 12797) (by norm_num)
        (q := 1 - (cell12797 ⟨38,by decide⟩).lower)
        (by norm_num [cell12797]) (by norm_num [cell12797])
      exact ⟨E.1,E.2.trans (by norm_num [cell12797])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy39 (n := 12797) (by norm_num)
        (q := 1 - (cell12797 ⟨39,by decide⟩).lower)
        (by norm_num [cell12797]) (by norm_num [cell12797])
      exact ⟨E.1,E.2.trans (by norm_num [cell12797])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy40 (n := 12797) (by norm_num)
        (q := 1 - (cell12797 ⟨40,by decide⟩).lower)
        (by norm_num [cell12797]) (by norm_num [cell12797])
      exact ⟨E.1,E.2.trans (by norm_num [cell12797])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy41 (n := 12797) (by norm_num)
        (q := 1 - (cell12797 ⟨41,by decide⟩).lower)
        (by norm_num [cell12797]) (by norm_num [cell12797])
      exact ⟨E.1,E.2.trans (by norm_num [cell12797])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy42 (n := 12797) (by norm_num)
        (q := 1 - (cell12797 ⟨42,by decide⟩).lower)
        (by norm_num [cell12797]) (by norm_num [cell12797])
      exact ⟨E.1,E.2.trans (by norm_num [cell12797])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy43 (n := 12797) (by norm_num)
        (q := 1 - (cell12797 ⟨43,by decide⟩).lower)
        (by norm_num [cell12797]) (by norm_num [cell12797])
      exact ⟨E.1,E.2.trans (by norm_num [cell12797])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy44 (n := 12797) (by norm_num)
        (q := 1 - (cell12797 ⟨44,by decide⟩).lower)
        (by norm_num [cell12797]) (by norm_num [cell12797])
      exact ⟨E.1,E.2.trans (by norm_num [cell12797])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy45 (n := 12797) (by norm_num)
        (q := 1 - (cell12797 ⟨45,by decide⟩).lower)
        (by norm_num [cell12797]) (by norm_num [cell12797])
      exact ⟨E.1,E.2.trans (by norm_num [cell12797])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy46 (n := 12797) (by norm_num)
        (q := 1 - (cell12797 ⟨46,by decide⟩).lower)
        (by norm_num [cell12797]) (by norm_num [cell12797])
      exact ⟨E.1,E.2.trans (by norm_num [cell12797])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy47 (n := 12797) (by norm_num)
        (q := 1 - (cell12797 ⟨47,by decide⟩).lower)
        (by norm_num [cell12797]) (by norm_num [cell12797])
      exact ⟨E.1,E.2.trans (by norm_num [cell12797])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy48 (n := 12797) (by norm_num)
        (q := 1 - (cell12797 ⟨48,by decide⟩).lower)
        (by norm_num [cell12797]) (by norm_num [cell12797])
      exact ⟨E.1,E.2.trans (by norm_num [cell12797])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy49 (n := 12797) (by norm_num)
        (q := 1 - (cell12797 ⟨49,by decide⟩).lower)
        (by norm_num [cell12797]) (by norm_num [cell12797])
      exact ⟨E.1,E.2.trans (by norm_num [cell12797])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy50 (n := 12797) (by norm_num)
        (q := 1 - (cell12797 ⟨50,by decide⟩).lower)
        (by norm_num [cell12797]) (by norm_num [cell12797])
      exact ⟨E.1,E.2.trans (by norm_num [cell12797])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy51 (n := 12797) (by norm_num)
        (q := 1 - (cell12797 ⟨51,by decide⟩).lower)
        (by norm_num [cell12797]) (by norm_num [cell12797])
      exact ⟨E.1,E.2.trans (by norm_num [cell12797])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy52 (n := 12797) (by norm_num)
        (q := 1 - (cell12797 ⟨52,by decide⟩).lower)
        (by norm_num [cell12797]) (by norm_num [cell12797])
      exact ⟨E.1,E.2.trans (by norm_num [cell12797])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12797

/-! Source-cell containment and simple scalar guards at 12797. -/
namespace BstLean.Part269.N12797
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12797)
open BstLean.Part268 (cell12797)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12797 ⟨10,by decide⟩).lower ∧ (cell12797 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12797 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12797 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12797 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12797 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12797 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12797,cell12797,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12797 ⟨11,by decide⟩).lower ∧ (cell12797 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12797 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12797 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12797 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12797 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12797 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12797,cell12797,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12797 ⟨12,by decide⟩).lower ∧ (cell12797 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12797 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12797 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12797 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12797 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12797 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12797,cell12797,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12797 ⟨13,by decide⟩).lower ∧ (cell12797 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12797 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12797 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12797 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12797 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12797 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12797,cell12797,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12797 ⟨14,by decide⟩).lower ∧ (cell12797 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12797 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12797 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12797 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12797 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12797 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12797,cell12797,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12797 ⟨15,by decide⟩).lower ∧ (cell12797 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12797 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12797 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12797 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12797 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12797 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12797,cell12797,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12797 ⟨16,by decide⟩).lower ∧ (cell12797 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12797 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12797 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12797 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12797 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12797 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12797,cell12797,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12797 ⟨17,by decide⟩).lower ∧ (cell12797 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12797 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12797 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12797 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12797 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12797 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12797,cell12797,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12797 ⟨18,by decide⟩).lower ∧ (cell12797 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12797 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12797 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12797 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12797 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12797 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12797,cell12797,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12797 ⟨19,by decide⟩).lower ∧ (cell12797 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12797 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12797 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12797 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12797 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12797 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12797,cell12797,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12797 ⟨20,by decide⟩).lower ∧ (cell12797 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12797 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12797 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12797 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12797 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12797 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12797,cell12797,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12797 ⟨21,by decide⟩).lower ∧ (cell12797 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12797 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12797 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12797 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12797 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12797 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12797,cell12797,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12797 ⟨22,by decide⟩).lower ∧ (cell12797 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12797 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12797 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12797 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12797 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12797 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12797,cell12797,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12797 ⟨23,by decide⟩).lower ∧ (cell12797 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12797 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12797 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12797 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12797 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12797 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12797,cell12797,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12797 ⟨24,by decide⟩).lower ∧ (cell12797 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12797 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12797 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12797 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12797 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12797 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12797,cell12797,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12797 ⟨25,by decide⟩).lower ∧ (cell12797 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12797 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12797 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12797 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12797 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12797 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12797,cell12797,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12797 ⟨26,by decide⟩).lower ∧ (cell12797 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12797 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12797 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12797 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12797 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12797 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12797,cell12797,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12797 ⟨27,by decide⟩).lower ∧ (cell12797 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12797 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12797 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12797 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12797 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12797 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12797,cell12797,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12797 ⟨28,by decide⟩).lower ∧ (cell12797 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12797 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12797 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12797 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12797 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12797 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12797,cell12797,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12797 ⟨29,by decide⟩).lower ∧ (cell12797 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12797 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12797 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12797 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12797 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12797 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12797,cell12797,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12797 ⟨30,by decide⟩).lower ∧ (cell12797 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12797 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12797 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12797 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12797 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12797 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12797,cell12797,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12797 ⟨31,by decide⟩).lower ∧ (cell12797 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12797 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12797 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12797 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12797 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12797 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12797,cell12797,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12797 ⟨32,by decide⟩).lower ∧ (cell12797 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12797 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12797 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12797 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12797 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12797 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12797,cell12797,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12797 ⟨33,by decide⟩).lower ∧ (cell12797 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12797 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12797 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12797 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12797 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12797 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12797,cell12797,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12797 ⟨34,by decide⟩).lower ∧ (cell12797 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12797 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12797 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12797 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12797 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12797 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12797,cell12797,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12797 ⟨35,by decide⟩).lower ∧ (cell12797 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12797 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12797 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12797 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12797 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12797 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12797,cell12797,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12797 ⟨36,by decide⟩).lower ∧ (cell12797 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12797 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12797 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12797 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12797 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12797 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12797,cell12797,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12797 ⟨37,by decide⟩).lower ∧ (cell12797 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12797 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12797 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12797 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12797 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12797 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12797,cell12797,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12797 ⟨38,by decide⟩).lower ∧ (cell12797 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12797 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12797 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12797 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12797 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12797 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12797,cell12797,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12797 ⟨39,by decide⟩).lower ∧ (cell12797 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12797 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12797 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12797 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12797 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12797 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12797,cell12797,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12797 ⟨40,by decide⟩).lower ∧ (cell12797 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12797 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12797 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12797 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12797 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12797 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12797,cell12797,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12797 ⟨41,by decide⟩).lower ∧ (cell12797 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12797 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12797 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12797 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12797 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12797 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12797,cell12797,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12797 ⟨42,by decide⟩).lower ∧ (cell12797 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12797 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12797 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12797 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12797 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12797 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12797,cell12797,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12797 ⟨43,by decide⟩).lower ∧ (cell12797 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12797 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12797 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12797 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12797 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12797 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12797,cell12797,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12797 ⟨44,by decide⟩).lower ∧ (cell12797 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12797 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12797 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12797 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12797 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12797 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12797,cell12797,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12797 ⟨45,by decide⟩).lower ∧ (cell12797 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12797 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12797 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12797 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12797 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12797 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12797,cell12797,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12797 ⟨46,by decide⟩).lower ∧ (cell12797 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12797 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12797 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12797 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12797 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12797 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12797,cell12797,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12797 ⟨47,by decide⟩).lower ∧ (cell12797 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12797 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12797 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12797 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12797 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12797 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12797,cell12797,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12797 ⟨48,by decide⟩).lower ∧ (cell12797 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12797 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12797 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12797 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12797 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12797 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12797,cell12797,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12797 ⟨49,by decide⟩).lower ∧ (cell12797 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12797 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12797 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12797 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12797 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12797 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12797,cell12797,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12797 ⟨50,by decide⟩).lower ∧ (cell12797 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12797 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12797 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12797 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12797 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12797 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12797,cell12797,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12797 ⟨51,by decide⟩).lower ∧ (cell12797 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12797 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12797 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12797 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12797 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12797 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12797,cell12797,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12797 ⟨52,by decide⟩).lower ∧ (cell12797 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12797 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12797 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12797 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12797 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12797 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12797,cell12797,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12797 i).lower ∧
    (cell12797 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12797 i).upper ≤ (0.532 : ℝ) ∧
    (cell12797 i).centre ≤ (0.1 : ℝ) ∧ (cell12797 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12797 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12797 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12797

/-! The local source numeric instances at 12797 have no network premises. -/
namespace BstLean.Part269.N12797
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12797)
open BstLean.Part268 (cell12797)

noncomputable def sourceNumerics12797 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12797 (cell12797 i)
      scalarRow12797.M scalarRow12797.H scalarRow12797.xi := by
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
    energy_allowance := scalarRow12797.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12797]
    centre_nonneg := (scalarRow12797.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D17.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12797])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12797
/-! Actual 12798 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12798
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12798 ≤ (1.035670650355 : ℝ) := by
  have hr : (113.128245809788 : ℝ) ≤ √(12798 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.128245809788 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12798 12798 (11 / 1000) ≤
    (0.008449587405 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12798) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.128245809788 : ℝ) ≤ √(12798 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12798)
  have hdiv : K / √(12798 : ℝ) ≤ K / 113.128245809788 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.128245809788 ≤ (0.008449587405 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12798.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12798 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12798 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12798 := gPlus_lower 12798
end BstLean.Part269.N12798

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12798
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035670650354 : ℝ) ≤ wn 12798 := by
  have hn : √(12798 : ℝ) ≤ 113.128245809789 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12798 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.128245809789 ≤ 2 / √(12798 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000249918666 : ℝ) ≤ rhoBar 12798 BstLean.Part154.csC ∧
    rhoBar 12798 BstLean.Part154.csC ≤ 0.000249919053 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035670650354 : ℝ) / (1.295212 * 12798) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035670650355 : ℝ) / (1.29521 * 12798) := by gcongr
      _ ≤ (0.000249919053 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12798 BstLean.Part154.csC) ≤ 0.000999738672 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12798 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12798 BstLean.Part154.csC) (piBar (rhoBar 12798 BstLean.Part154.csC)) ≤ 0.000190889789 ∧
    cc1 (rhoBar 12798 BstLean.Part154.csC) (piBar (rhoBar 12798 BstLean.Part154.csC)) ≤ 0.000121464455 ∧
    cc2 (rhoBar 12798 BstLean.Part154.csC) ≤ 0.000070511064 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12798 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12798 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12798 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12798 BstLean.Part154.csC * nuR (rhoBar 12798 BstLean.Part154.csC)) ≤ 0.000499853721 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000249919053 : ℝ) * 0.000999738672 := by gcongr
      _ ≤ (0.000499853721 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12798 BstLean.Part154.csC) * nuR (rhoBar 12798 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000999738672 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12798 BstLean.Part154.csC) * rhoBar 12798 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000249919053 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000249919053 / 2 + 0.399 * 0.000999738672 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000190889789 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000499853721 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121464455 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000249919053 / 1.414213562 := by gcongr
      _ ≤ (0.000070511064 : ℝ) := by norm_num

end BstLean.Part269.N12798

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12798
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12798 BstLean.Part154.csC) (piBar (rhoBar 12798 BstLean.Part154.csC)) ≤ 1.57362E-7 := by
  have hr0 : 0 ≤ rhoBar 12798 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12798 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12798 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12798 BstLean.Part154.csC) (piBar (rhoBar 12798 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12798 BstLean.Part154.csC) (piBar (rhoBar 12798 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12798 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000190889789 : ℝ) ^ 2 + 0.000121464455 ^ 2 + 3 * 0.000070511064 ^ 2 +
        2 * 0.797885 * 0.000190889789 * 0.000121464455 + 2 * 0.000190889789 * 0.000070511064 +
        4 * 0.797885 * 0.000121464455 * 0.000070511064 := by gcongr
    _ ≤ (1.57362E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12798 BstLean.Part154.csC Θ ≤ 0.002608451902 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12798 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12798 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12798 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12798 BstLean.Part154.csC) (piBar (rhoBar 12798 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12798 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035670650355 * 1.57362E-7 / (0.000249918666 : ℝ) := by gcongr
    _ ≤ 0.002608451902 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12798 BstLean.Part154.csC Θ ≤ 0.002893835508 + 0.000659115069 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12798 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12798 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12798 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035670650355 : ℝ) * ((2 * Θ * 0.000249919053 +
        (6863 / 10000) * 0.000249919053 * 12798 * 0.000999738672) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002893835508 + 0.000659115069 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12798 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12798 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12798 0.011 Θ ∧ gammaRatio 12798 0.011 Θ ≤ 0.000085915708 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12798 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035670650355 : ℝ) * 0.525 / ((1 - 0.011) * 12798) := by gcongr
      _ ≤ (0.000085915708 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12798 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12798 0.011 Θ) :=
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
    badAllowance 12798 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000560204559 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12798 BstLean.Part154.csC) 1.22 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 2 (rhoBar 12798 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12798 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12798 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12798 0.011 Θ) 1.12 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 1 (gammaRatio 12798 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12798 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12798 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12798 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12798 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035670650355 : ℝ) * 12798 *
        (1.8602E-8 / 1.1045361 + 2.2721E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000560204559 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12798 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003454040067 + 0.003267566971 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12798

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12798
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12798 BstLean.Part154.csC) (piBar (rhoBar 12798 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12798 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12798 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12798 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12798 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12798 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12798 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12798 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12798 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12798 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12798 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12798 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12798 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12798 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12798 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052280803940 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12798) ≤ 0.010556493408 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12798 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035670650355)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010556493408 + 2 * 0.737676 / 12798) := by gcongr
    _ ≤ (0.052280803940 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12798 12 ≤ 0.0015 := by
  exact BstLean.Part269.S17.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12798

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12798
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560507966205 : ℝ) ≤ plow 12798 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12798) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052676112727)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001369437249) : eMP 12798 0.011 xi bn ≤ 0.001179096723 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12798 : ℝ) * (1 - 0.011))) ≤ 0.000583011109 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001369437249 / (12798 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000583011109 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000583011109 : ℝ) + 3.141593 * 0.052676112727 / (12798 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001179096723 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052676112727)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001369437249) : PiBarMP 12798 12 0.011 xi bn ≤ 0.160626377118 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12798 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037005908299 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.504319917059 : ℝ) ≤ √((12798 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.128245809788 : ℝ) ≤ √(12798 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12798) ≤ 0.123155876440 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037005908299 + 0.052676112727 * 1.772454 / (2 * (112.504319917059 : ℝ))) * (1 + 0.001179096723) +
        8 / (12798 * 113.128245809788) + 0.123155876440 := by gcongr
    _ ≤ (0.160626377118 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052676112727)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001369437249) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281793576411) :
    parallelOracle 12798 0.011 xi bn cd ≤ 0.161609443754 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12798 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12798 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560507966205 : ℝ) ≤ plow 12798 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.128245809788 : ℝ) ≤ √(12798 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281793576411 : ℝ) / (2 * 0.560507966205 * 113.128245809788)) * 0.160626377118 +
        0.281793576411 ^ 2 / (2 * 0.560507966205 * 113.128245809788) := by gcongr
    _ ≤ (0.161609443754 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052676112727) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001369437249)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281793576411) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12798 12798 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560507966205 : ℝ) ≤ plow 12798 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.128245809788 : ℝ) ≤ √(12798 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12798 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12798 Θ 1.22 ≤ 0.011722099026 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.128245809788 := by gcongr <;> linarith
      _ ≤ (0.011722099026 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12798 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12798 12798 0.011 ≤ 0.008449587405 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12798 12798 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12798 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12798 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12798 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12798 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161609443754 + 0.011722099026 + (0.008449587405 : ℝ) *
        (1 + 2 * (0.281793576411 + 0.011722099026) / (0.560507966205 * 113.128245809788))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12798]

end BstLean.Part269.N12798

/-! The original eight local profiles supply actual 12798 moment certificates. -/
namespace BstLean.Part269.N12798
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12798 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12798 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12798 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052676112727 ∧
    0 ≤ bN 12798 BstLean.Part154.csC (groupTheta g) ∧ bN 12798 BstLean.Part154.csC (groupTheta g) ≤ 0.001369437249 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12798 12798 0.011
      (momentAllowance 12798 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12798 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12798 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12798 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12798 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12798 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229512772471 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12798 0.011
      (momentAllowance 12798 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12798 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12798
/-! The actual computed-centre upper energy formula at 12798. -/
namespace BstLean.Part269.N12798
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12798

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12798
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12798)
open BstLean.Part268 (cell12798)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085209497518
  | 2 => 0.086147200963
  | 3 => 0.087082326223
  | 4 => 0.088016124738
  | 5 => 0.088950115477
  | 6 => 0.089886125357
  | 7 => 0.090826333580
  | 8 => 0.091773319972
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12798 12798 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12798 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003459522332 + 0.003273654356 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S17.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12798

/-! Actual upper energy certificates on all 43 source endpoints at 12798. -/
namespace BstLean.Part269.N12798
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12798)
open BstLean.Part268 (cell12798)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12798 (gMinus 12798) (1 - (cell12798 i).lower) ≤ 1 ∧
    energyUpper 12798 (gMinus 12798) (BstLean.Part211.gPlus 12798)
      (finiteEnergy 12798 12798 0.011) (1 - (cell12798 i).lower) ≤
      (cell12798 i).energy := by
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
      have E := BstLean.Part269.S17.uniformEnergy10 (n := 12798) (by norm_num)
        (q := 1 - (cell12798 ⟨10,by decide⟩).lower)
        (by norm_num [cell12798]) (by norm_num [cell12798])
      exact ⟨E.1,E.2.trans (by norm_num [cell12798])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy11 (n := 12798) (by norm_num)
        (q := 1 - (cell12798 ⟨11,by decide⟩).lower)
        (by norm_num [cell12798]) (by norm_num [cell12798])
      exact ⟨E.1,E.2.trans (by norm_num [cell12798])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy12 (n := 12798) (by norm_num)
        (q := 1 - (cell12798 ⟨12,by decide⟩).lower)
        (by norm_num [cell12798]) (by norm_num [cell12798])
      exact ⟨E.1,E.2.trans (by norm_num [cell12798])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy13 (n := 12798) (by norm_num)
        (q := 1 - (cell12798 ⟨13,by decide⟩).lower)
        (by norm_num [cell12798]) (by norm_num [cell12798])
      exact ⟨E.1,E.2.trans (by norm_num [cell12798])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy14 (n := 12798) (by norm_num)
        (q := 1 - (cell12798 ⟨14,by decide⟩).lower)
        (by norm_num [cell12798]) (by norm_num [cell12798])
      exact ⟨E.1,E.2.trans (by norm_num [cell12798])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy15 (n := 12798) (by norm_num)
        (q := 1 - (cell12798 ⟨15,by decide⟩).lower)
        (by norm_num [cell12798]) (by norm_num [cell12798])
      exact ⟨E.1,E.2.trans (by norm_num [cell12798])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy16 (n := 12798) (by norm_num)
        (q := 1 - (cell12798 ⟨16,by decide⟩).lower)
        (by norm_num [cell12798]) (by norm_num [cell12798])
      exact ⟨E.1,E.2.trans (by norm_num [cell12798])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy17 (n := 12798) (by norm_num)
        (q := 1 - (cell12798 ⟨17,by decide⟩).lower)
        (by norm_num [cell12798]) (by norm_num [cell12798])
      exact ⟨E.1,E.2.trans (by norm_num [cell12798])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy18 (n := 12798) (by norm_num)
        (q := 1 - (cell12798 ⟨18,by decide⟩).lower)
        (by norm_num [cell12798]) (by norm_num [cell12798])
      exact ⟨E.1,E.2.trans (by norm_num [cell12798])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy19 (n := 12798) (by norm_num)
        (q := 1 - (cell12798 ⟨19,by decide⟩).lower)
        (by norm_num [cell12798]) (by norm_num [cell12798])
      exact ⟨E.1,E.2.trans (by norm_num [cell12798])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy20 (n := 12798) (by norm_num)
        (q := 1 - (cell12798 ⟨20,by decide⟩).lower)
        (by norm_num [cell12798]) (by norm_num [cell12798])
      exact ⟨E.1,E.2.trans (by norm_num [cell12798])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy21 (n := 12798) (by norm_num)
        (q := 1 - (cell12798 ⟨21,by decide⟩).lower)
        (by norm_num [cell12798]) (by norm_num [cell12798])
      exact ⟨E.1,E.2.trans (by norm_num [cell12798])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy22 (n := 12798) (by norm_num)
        (q := 1 - (cell12798 ⟨22,by decide⟩).lower)
        (by norm_num [cell12798]) (by norm_num [cell12798])
      exact ⟨E.1,E.2.trans (by norm_num [cell12798])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy23 (n := 12798) (by norm_num)
        (q := 1 - (cell12798 ⟨23,by decide⟩).lower)
        (by norm_num [cell12798]) (by norm_num [cell12798])
      exact ⟨E.1,E.2.trans (by norm_num [cell12798])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy24 (n := 12798) (by norm_num)
        (q := 1 - (cell12798 ⟨24,by decide⟩).lower)
        (by norm_num [cell12798]) (by norm_num [cell12798])
      exact ⟨E.1,E.2.trans (by norm_num [cell12798])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy25 (n := 12798) (by norm_num)
        (q := 1 - (cell12798 ⟨25,by decide⟩).lower)
        (by norm_num [cell12798]) (by norm_num [cell12798])
      exact ⟨E.1,E.2.trans (by norm_num [cell12798])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy26 (n := 12798) (by norm_num)
        (q := 1 - (cell12798 ⟨26,by decide⟩).lower)
        (by norm_num [cell12798]) (by norm_num [cell12798])
      exact ⟨E.1,E.2.trans (by norm_num [cell12798])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy27 (n := 12798) (by norm_num)
        (q := 1 - (cell12798 ⟨27,by decide⟩).lower)
        (by norm_num [cell12798]) (by norm_num [cell12798])
      exact ⟨E.1,E.2.trans (by norm_num [cell12798])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy28 (n := 12798) (by norm_num)
        (q := 1 - (cell12798 ⟨28,by decide⟩).lower)
        (by norm_num [cell12798]) (by norm_num [cell12798])
      exact ⟨E.1,E.2.trans (by norm_num [cell12798])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy29 (n := 12798) (by norm_num)
        (q := 1 - (cell12798 ⟨29,by decide⟩).lower)
        (by norm_num [cell12798]) (by norm_num [cell12798])
      exact ⟨E.1,E.2.trans (by norm_num [cell12798])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy30 (n := 12798) (by norm_num)
        (q := 1 - (cell12798 ⟨30,by decide⟩).lower)
        (by norm_num [cell12798]) (by norm_num [cell12798])
      exact ⟨E.1,E.2.trans (by norm_num [cell12798])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy31 (n := 12798) (by norm_num)
        (q := 1 - (cell12798 ⟨31,by decide⟩).lower)
        (by norm_num [cell12798]) (by norm_num [cell12798])
      exact ⟨E.1,E.2.trans (by norm_num [cell12798])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy32 (n := 12798) (by norm_num)
        (q := 1 - (cell12798 ⟨32,by decide⟩).lower)
        (by norm_num [cell12798]) (by norm_num [cell12798])
      exact ⟨E.1,E.2.trans (by norm_num [cell12798])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy33 (n := 12798) (by norm_num)
        (q := 1 - (cell12798 ⟨33,by decide⟩).lower)
        (by norm_num [cell12798]) (by norm_num [cell12798])
      exact ⟨E.1,E.2.trans (by norm_num [cell12798])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy34 (n := 12798) (by norm_num)
        (q := 1 - (cell12798 ⟨34,by decide⟩).lower)
        (by norm_num [cell12798]) (by norm_num [cell12798])
      exact ⟨E.1,E.2.trans (by norm_num [cell12798])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy35 (n := 12798) (by norm_num)
        (q := 1 - (cell12798 ⟨35,by decide⟩).lower)
        (by norm_num [cell12798]) (by norm_num [cell12798])
      exact ⟨E.1,E.2.trans (by norm_num [cell12798])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy36 (n := 12798) (by norm_num)
        (q := 1 - (cell12798 ⟨36,by decide⟩).lower)
        (by norm_num [cell12798]) (by norm_num [cell12798])
      exact ⟨E.1,E.2.trans (by norm_num [cell12798])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy37 (n := 12798) (by norm_num)
        (q := 1 - (cell12798 ⟨37,by decide⟩).lower)
        (by norm_num [cell12798]) (by norm_num [cell12798])
      exact ⟨E.1,E.2.trans (by norm_num [cell12798])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy38 (n := 12798) (by norm_num)
        (q := 1 - (cell12798 ⟨38,by decide⟩).lower)
        (by norm_num [cell12798]) (by norm_num [cell12798])
      exact ⟨E.1,E.2.trans (by norm_num [cell12798])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy39 (n := 12798) (by norm_num)
        (q := 1 - (cell12798 ⟨39,by decide⟩).lower)
        (by norm_num [cell12798]) (by norm_num [cell12798])
      exact ⟨E.1,E.2.trans (by norm_num [cell12798])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy40 (n := 12798) (by norm_num)
        (q := 1 - (cell12798 ⟨40,by decide⟩).lower)
        (by norm_num [cell12798]) (by norm_num [cell12798])
      exact ⟨E.1,E.2.trans (by norm_num [cell12798])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy41 (n := 12798) (by norm_num)
        (q := 1 - (cell12798 ⟨41,by decide⟩).lower)
        (by norm_num [cell12798]) (by norm_num [cell12798])
      exact ⟨E.1,E.2.trans (by norm_num [cell12798])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy42 (n := 12798) (by norm_num)
        (q := 1 - (cell12798 ⟨42,by decide⟩).lower)
        (by norm_num [cell12798]) (by norm_num [cell12798])
      exact ⟨E.1,E.2.trans (by norm_num [cell12798])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy43 (n := 12798) (by norm_num)
        (q := 1 - (cell12798 ⟨43,by decide⟩).lower)
        (by norm_num [cell12798]) (by norm_num [cell12798])
      exact ⟨E.1,E.2.trans (by norm_num [cell12798])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy44 (n := 12798) (by norm_num)
        (q := 1 - (cell12798 ⟨44,by decide⟩).lower)
        (by norm_num [cell12798]) (by norm_num [cell12798])
      exact ⟨E.1,E.2.trans (by norm_num [cell12798])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy45 (n := 12798) (by norm_num)
        (q := 1 - (cell12798 ⟨45,by decide⟩).lower)
        (by norm_num [cell12798]) (by norm_num [cell12798])
      exact ⟨E.1,E.2.trans (by norm_num [cell12798])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy46 (n := 12798) (by norm_num)
        (q := 1 - (cell12798 ⟨46,by decide⟩).lower)
        (by norm_num [cell12798]) (by norm_num [cell12798])
      exact ⟨E.1,E.2.trans (by norm_num [cell12798])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy47 (n := 12798) (by norm_num)
        (q := 1 - (cell12798 ⟨47,by decide⟩).lower)
        (by norm_num [cell12798]) (by norm_num [cell12798])
      exact ⟨E.1,E.2.trans (by norm_num [cell12798])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy48 (n := 12798) (by norm_num)
        (q := 1 - (cell12798 ⟨48,by decide⟩).lower)
        (by norm_num [cell12798]) (by norm_num [cell12798])
      exact ⟨E.1,E.2.trans (by norm_num [cell12798])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy49 (n := 12798) (by norm_num)
        (q := 1 - (cell12798 ⟨49,by decide⟩).lower)
        (by norm_num [cell12798]) (by norm_num [cell12798])
      exact ⟨E.1,E.2.trans (by norm_num [cell12798])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy50 (n := 12798) (by norm_num)
        (q := 1 - (cell12798 ⟨50,by decide⟩).lower)
        (by norm_num [cell12798]) (by norm_num [cell12798])
      exact ⟨E.1,E.2.trans (by norm_num [cell12798])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy51 (n := 12798) (by norm_num)
        (q := 1 - (cell12798 ⟨51,by decide⟩).lower)
        (by norm_num [cell12798]) (by norm_num [cell12798])
      exact ⟨E.1,E.2.trans (by norm_num [cell12798])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy52 (n := 12798) (by norm_num)
        (q := 1 - (cell12798 ⟨52,by decide⟩).lower)
        (by norm_num [cell12798]) (by norm_num [cell12798])
      exact ⟨E.1,E.2.trans (by norm_num [cell12798])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12798

/-! Source-cell containment and simple scalar guards at 12798. -/
namespace BstLean.Part269.N12798
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12798)
open BstLean.Part268 (cell12798)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12798 ⟨10,by decide⟩).lower ∧ (cell12798 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12798 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12798 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12798 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12798 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12798 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12798,cell12798,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12798 ⟨11,by decide⟩).lower ∧ (cell12798 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12798 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12798 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12798 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12798 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12798 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12798,cell12798,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12798 ⟨12,by decide⟩).lower ∧ (cell12798 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12798 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12798 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12798 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12798 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12798 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12798,cell12798,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12798 ⟨13,by decide⟩).lower ∧ (cell12798 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12798 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12798 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12798 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12798 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12798 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12798,cell12798,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12798 ⟨14,by decide⟩).lower ∧ (cell12798 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12798 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12798 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12798 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12798 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12798 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12798,cell12798,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12798 ⟨15,by decide⟩).lower ∧ (cell12798 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12798 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12798 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12798 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12798 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12798 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12798,cell12798,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12798 ⟨16,by decide⟩).lower ∧ (cell12798 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12798 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12798 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12798 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12798 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12798 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12798,cell12798,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12798 ⟨17,by decide⟩).lower ∧ (cell12798 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12798 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12798 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12798 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12798 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12798 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12798,cell12798,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12798 ⟨18,by decide⟩).lower ∧ (cell12798 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12798 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12798 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12798 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12798 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12798 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12798,cell12798,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12798 ⟨19,by decide⟩).lower ∧ (cell12798 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12798 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12798 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12798 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12798 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12798 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12798,cell12798,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12798 ⟨20,by decide⟩).lower ∧ (cell12798 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12798 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12798 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12798 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12798 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12798 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12798,cell12798,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12798 ⟨21,by decide⟩).lower ∧ (cell12798 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12798 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12798 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12798 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12798 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12798 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12798,cell12798,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12798 ⟨22,by decide⟩).lower ∧ (cell12798 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12798 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12798 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12798 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12798 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12798 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12798,cell12798,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12798 ⟨23,by decide⟩).lower ∧ (cell12798 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12798 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12798 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12798 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12798 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12798 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12798,cell12798,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12798 ⟨24,by decide⟩).lower ∧ (cell12798 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12798 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12798 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12798 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12798 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12798 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12798,cell12798,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12798 ⟨25,by decide⟩).lower ∧ (cell12798 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12798 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12798 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12798 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12798 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12798 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12798,cell12798,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12798 ⟨26,by decide⟩).lower ∧ (cell12798 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12798 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12798 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12798 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12798 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12798 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12798,cell12798,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12798 ⟨27,by decide⟩).lower ∧ (cell12798 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12798 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12798 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12798 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12798 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12798 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12798,cell12798,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12798 ⟨28,by decide⟩).lower ∧ (cell12798 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12798 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12798 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12798 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12798 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12798 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12798,cell12798,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12798 ⟨29,by decide⟩).lower ∧ (cell12798 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12798 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12798 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12798 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12798 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12798 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12798,cell12798,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12798 ⟨30,by decide⟩).lower ∧ (cell12798 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12798 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12798 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12798 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12798 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12798 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12798,cell12798,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12798 ⟨31,by decide⟩).lower ∧ (cell12798 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12798 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12798 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12798 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12798 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12798 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12798,cell12798,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12798 ⟨32,by decide⟩).lower ∧ (cell12798 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12798 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12798 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12798 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12798 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12798 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12798,cell12798,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12798 ⟨33,by decide⟩).lower ∧ (cell12798 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12798 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12798 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12798 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12798 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12798 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12798,cell12798,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12798 ⟨34,by decide⟩).lower ∧ (cell12798 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12798 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12798 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12798 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12798 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12798 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12798,cell12798,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12798 ⟨35,by decide⟩).lower ∧ (cell12798 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12798 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12798 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12798 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12798 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12798 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12798,cell12798,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12798 ⟨36,by decide⟩).lower ∧ (cell12798 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12798 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12798 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12798 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12798 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12798 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12798,cell12798,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12798 ⟨37,by decide⟩).lower ∧ (cell12798 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12798 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12798 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12798 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12798 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12798 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12798,cell12798,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12798 ⟨38,by decide⟩).lower ∧ (cell12798 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12798 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12798 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12798 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12798 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12798 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12798,cell12798,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12798 ⟨39,by decide⟩).lower ∧ (cell12798 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12798 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12798 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12798 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12798 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12798 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12798,cell12798,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12798 ⟨40,by decide⟩).lower ∧ (cell12798 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12798 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12798 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12798 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12798 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12798 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12798,cell12798,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12798 ⟨41,by decide⟩).lower ∧ (cell12798 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12798 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12798 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12798 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12798 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12798 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12798,cell12798,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12798 ⟨42,by decide⟩).lower ∧ (cell12798 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12798 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12798 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12798 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12798 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12798 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12798,cell12798,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12798 ⟨43,by decide⟩).lower ∧ (cell12798 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12798 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12798 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12798 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12798 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12798 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12798,cell12798,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12798 ⟨44,by decide⟩).lower ∧ (cell12798 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12798 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12798 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12798 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12798 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12798 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12798,cell12798,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12798 ⟨45,by decide⟩).lower ∧ (cell12798 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12798 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12798 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12798 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12798 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12798 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12798,cell12798,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12798 ⟨46,by decide⟩).lower ∧ (cell12798 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12798 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12798 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12798 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12798 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12798 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12798,cell12798,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12798 ⟨47,by decide⟩).lower ∧ (cell12798 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12798 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12798 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12798 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12798 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12798 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12798,cell12798,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12798 ⟨48,by decide⟩).lower ∧ (cell12798 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12798 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12798 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12798 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12798 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12798 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12798,cell12798,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12798 ⟨49,by decide⟩).lower ∧ (cell12798 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12798 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12798 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12798 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12798 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12798 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12798,cell12798,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12798 ⟨50,by decide⟩).lower ∧ (cell12798 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12798 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12798 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12798 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12798 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12798 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12798,cell12798,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12798 ⟨51,by decide⟩).lower ∧ (cell12798 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12798 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12798 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12798 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12798 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12798 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12798,cell12798,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12798 ⟨52,by decide⟩).lower ∧ (cell12798 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12798 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12798 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12798 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12798 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12798 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12798,cell12798,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12798 i).lower ∧
    (cell12798 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12798 i).upper ≤ (0.532 : ℝ) ∧
    (cell12798 i).centre ≤ (0.1 : ℝ) ∧ (cell12798 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12798 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12798 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12798

/-! The local source numeric instances at 12798 have no network premises. -/
namespace BstLean.Part269.N12798
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12798)
open BstLean.Part268 (cell12798)

noncomputable def sourceNumerics12798 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12798 (cell12798 i)
      scalarRow12798.M scalarRow12798.H scalarRow12798.xi := by
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
    energy_allowance := scalarRow12798.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12798]
    centre_nonneg := (scalarRow12798.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D17.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12798])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12798
/-! Actual 12799 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12799
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12799 ≤ (1.035669244625 : ℝ) := by
  have hr : (113.132665486145 : ℝ) ≤ √(12799 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.132665486145 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12799 12799 (11 / 1000) ≤
    (0.008449257309 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12799) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.132665486145 : ℝ) ≤ √(12799 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12799)
  have hdiv : K / √(12799 : ℝ) ≤ K / 113.132665486145 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.132665486145 ≤ (0.008449257309 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12799.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12799 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12799 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12799 := gPlus_lower 12799
end BstLean.Part269.N12799

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12799
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035669244624 : ℝ) ≤ wn 12799 := by
  have hn : √(12799 : ℝ) ≤ 113.132665486146 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12799 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.132665486146 ≤ 2 / √(12799 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000249898800 : ℝ) ≤ rhoBar 12799 BstLean.Part154.csC ∧
    rhoBar 12799 BstLean.Part154.csC ≤ 0.000249899187 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035669244624 : ℝ) / (1.295212 * 12799) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035669244625 : ℝ) / (1.29521 * 12799) := by gcongr
      _ ≤ (0.000249899187 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12799 BstLean.Part154.csC) ≤ 0.000999659198 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12799 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12799 BstLean.Part154.csC) (piBar (rhoBar 12799 BstLean.Part154.csC)) ≤ 0.000190874615 ∧
    cc1 (rhoBar 12799 BstLean.Part154.csC) (piBar (rhoBar 12799 BstLean.Part154.csC)) ≤ 0.000121454799 ∧
    cc2 (rhoBar 12799 BstLean.Part154.csC) ≤ 0.000070505459 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12799 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12799 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12799 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12799 BstLean.Part154.csC * nuR (rhoBar 12799 BstLean.Part154.csC)) ≤ 0.000499813987 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000249899187 : ℝ) * 0.000999659198 := by gcongr
      _ ≤ (0.000499813987 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12799 BstLean.Part154.csC) * nuR (rhoBar 12799 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000999659198 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12799 BstLean.Part154.csC) * rhoBar 12799 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000249899187 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000249899187 / 2 + 0.399 * 0.000999659198 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000190874615 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000499813987 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121454799 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000249899187 / 1.414213562 := by gcongr
      _ ≤ (0.000070505459 : ℝ) := by norm_num

end BstLean.Part269.N12799

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12799
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12799 BstLean.Part154.csC) (piBar (rhoBar 12799 BstLean.Part154.csC)) ≤ 1.57337E-7 := by
  have hr0 : 0 ≤ rhoBar 12799 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12799 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12799 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12799 BstLean.Part154.csC) (piBar (rhoBar 12799 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12799 BstLean.Part154.csC) (piBar (rhoBar 12799 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12799 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000190874615 : ℝ) ^ 2 + 0.000121454799 ^ 2 + 3 * 0.000070505459 ^ 2 +
        2 * 0.797885 * 0.000190874615 * 0.000121454799 + 2 * 0.000190874615 * 0.000070505459 +
        4 * 0.797885 * 0.000121454799 * 0.000070505459 := by gcongr
    _ ≤ (1.57337E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12799 BstLean.Part154.csC Θ ≤ 0.002608241288 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12799 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12799 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12799 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12799 BstLean.Part154.csC) (piBar (rhoBar 12799 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12799 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035669244625 * 1.57337E-7 / (0.000249898800 : ℝ) := by gcongr
    _ ≤ 0.002608241288 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12799 BstLean.Part154.csC Θ ≤ 0.002893597604 + 0.000659061781 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12799 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12799 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12799 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035669244625 : ℝ) * ((2 * Θ * 0.000249899187 +
        (6863 / 10000) * 0.000249899187 * 12799 * 0.000999659198) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002893597604 + 0.000659061781 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12799 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12799 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12799 0.011 Θ ∧ gammaRatio 12799 0.011 Θ ≤ 0.000085908879 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12799 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035669244625 : ℝ) * 0.525 / ((1 - 0.011) * 12799) := by gcongr
      _ ≤ (0.000085908879 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12799 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12799 0.011 Θ) :=
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
    badAllowance 12799 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000560204559 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12799 BstLean.Part154.csC) 1.22 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 2 (rhoBar 12799 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12799 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12799 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12799 0.011 Θ) 1.12 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 1 (gammaRatio 12799 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12799 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12799 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12799 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12799 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035669244625 : ℝ) * 12799 *
        (1.8602E-8 / 1.1045361 + 2.2721E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000560204559 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12799 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003453802163 + 0.003267303069 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12799

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12799
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12799 BstLean.Part154.csC) (piBar (rhoBar 12799 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12799 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12799 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12799 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12799 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12799 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12799 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12799 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12799 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12799 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12799 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12799 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12799 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12799 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12799 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052278739456 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12799) ≤ 0.010556081004 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12799 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035669244625)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010556081004 + 2 * 0.737676 / 12799) := by gcongr
    _ ≤ (0.052278739456 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12799 12 ≤ 0.0015 := by
  exact BstLean.Part269.S17.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12799

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12799
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560508010735 : ℝ) ≤ plow 12799 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12799) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052675736275)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001369326677) : eMP 12799 0.011 xi bn ≤ 0.001179002984 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12799 : ℝ) * (1 - 0.011))) ≤ 0.000582964797 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001369326677 / (12799 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000582964797 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000582964797 : ℝ) + 3.141593 * 0.052675736275 / (12799 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001179002984 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052675736275)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001369326677) : PiBarMP 12799 12 0.011 xi bn ≤ 0.160620046749 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12799 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037004414291 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.508715217977 : ℝ) ≤ √((12799 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.132665486145 : ℝ) ≤ √(12799 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12799) ≤ 0.123151065194 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037004414291 + 0.052675736275 * 1.772454 / (2 * (112.508715217977 : ℝ))) * (1 + 0.001179002984) +
        8 / (12799 * 113.132665486145) + 0.123151065194 := by gcongr
    _ ≤ (0.160620046749 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052675736275)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001369326677) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281790691814) :
    parallelOracle 12799 0.011 xi bn cd ≤ 0.161603044365 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12799 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12799 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560508010735 : ℝ) ≤ plow 12799 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.132665486145 : ℝ) ≤ √(12799 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281790691814 : ℝ) / (2 * 0.560508010735 * 113.132665486145)) * 0.160620046749 +
        0.281790691814 ^ 2 / (2 * 0.560508010735 * 113.132665486145) := by gcongr
    _ ≤ (0.161603044365 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052675736275) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001369326677)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281790691814) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12799 12799 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560508010735 : ℝ) ≤ plow 12799 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.132665486145 : ℝ) ≤ √(12799 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12799 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12799 Θ 1.22 ≤ 0.011721641087 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.132665486145 := by gcongr <;> linarith
      _ ≤ (0.011721641087 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12799 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12799 12799 0.011 ≤ 0.008449257309 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12799 12799 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12799 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12799 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12799 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12799 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161603044365 + 0.011721641087 + (0.008449257309 : ℝ) *
        (1 + 2 * (0.281790691814 + 0.011721641087) / (0.560508010735 * 113.132665486145))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12799]

end BstLean.Part269.N12799

/-! The original eight local profiles supply actual 12799 moment certificates. -/
namespace BstLean.Part269.N12799
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12799 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12799 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12799 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052675736275 ∧
    0 ≤ bN 12799 BstLean.Part154.csC (groupTheta g) ∧ bN 12799 BstLean.Part154.csC (groupTheta g) ≤ 0.001369326677 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12799 12799 0.011
      (momentAllowance 12799 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12799 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12799 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12799 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12799 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12799 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229511952358 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12799 0.011
      (momentAllowance 12799 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12799 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12799
/-! The actual computed-centre upper energy formula at 12799. -/
namespace BstLean.Part269.N12799
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12799

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12799
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12799)
open BstLean.Part268 (cell12799)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085206682884
  | 2 => 0.086144336865
  | 3 => 0.087079405812
  | 4 => 0.088013139563
  | 5 => 0.088947055197
  | 6 => 0.089882977417
  | 7 => 0.090823082851
  | 8 => 0.091769948342
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12799 12799 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12799 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003459522332 + 0.003273654356 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S17.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12799

/-! Actual upper energy certificates on all 43 source endpoints at 12799. -/
namespace BstLean.Part269.N12799
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12799)
open BstLean.Part268 (cell12799)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12799 (gMinus 12799) (1 - (cell12799 i).lower) ≤ 1 ∧
    energyUpper 12799 (gMinus 12799) (BstLean.Part211.gPlus 12799)
      (finiteEnergy 12799 12799 0.011) (1 - (cell12799 i).lower) ≤
      (cell12799 i).energy := by
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
      have E := BstLean.Part269.S17.uniformEnergy10 (n := 12799) (by norm_num)
        (q := 1 - (cell12799 ⟨10,by decide⟩).lower)
        (by norm_num [cell12799]) (by norm_num [cell12799])
      exact ⟨E.1,E.2.trans (by norm_num [cell12799])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy11 (n := 12799) (by norm_num)
        (q := 1 - (cell12799 ⟨11,by decide⟩).lower)
        (by norm_num [cell12799]) (by norm_num [cell12799])
      exact ⟨E.1,E.2.trans (by norm_num [cell12799])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy12 (n := 12799) (by norm_num)
        (q := 1 - (cell12799 ⟨12,by decide⟩).lower)
        (by norm_num [cell12799]) (by norm_num [cell12799])
      exact ⟨E.1,E.2.trans (by norm_num [cell12799])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy13 (n := 12799) (by norm_num)
        (q := 1 - (cell12799 ⟨13,by decide⟩).lower)
        (by norm_num [cell12799]) (by norm_num [cell12799])
      exact ⟨E.1,E.2.trans (by norm_num [cell12799])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy14 (n := 12799) (by norm_num)
        (q := 1 - (cell12799 ⟨14,by decide⟩).lower)
        (by norm_num [cell12799]) (by norm_num [cell12799])
      exact ⟨E.1,E.2.trans (by norm_num [cell12799])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy15 (n := 12799) (by norm_num)
        (q := 1 - (cell12799 ⟨15,by decide⟩).lower)
        (by norm_num [cell12799]) (by norm_num [cell12799])
      exact ⟨E.1,E.2.trans (by norm_num [cell12799])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy16 (n := 12799) (by norm_num)
        (q := 1 - (cell12799 ⟨16,by decide⟩).lower)
        (by norm_num [cell12799]) (by norm_num [cell12799])
      exact ⟨E.1,E.2.trans (by norm_num [cell12799])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy17 (n := 12799) (by norm_num)
        (q := 1 - (cell12799 ⟨17,by decide⟩).lower)
        (by norm_num [cell12799]) (by norm_num [cell12799])
      exact ⟨E.1,E.2.trans (by norm_num [cell12799])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy18 (n := 12799) (by norm_num)
        (q := 1 - (cell12799 ⟨18,by decide⟩).lower)
        (by norm_num [cell12799]) (by norm_num [cell12799])
      exact ⟨E.1,E.2.trans (by norm_num [cell12799])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy19 (n := 12799) (by norm_num)
        (q := 1 - (cell12799 ⟨19,by decide⟩).lower)
        (by norm_num [cell12799]) (by norm_num [cell12799])
      exact ⟨E.1,E.2.trans (by norm_num [cell12799])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy20 (n := 12799) (by norm_num)
        (q := 1 - (cell12799 ⟨20,by decide⟩).lower)
        (by norm_num [cell12799]) (by norm_num [cell12799])
      exact ⟨E.1,E.2.trans (by norm_num [cell12799])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy21 (n := 12799) (by norm_num)
        (q := 1 - (cell12799 ⟨21,by decide⟩).lower)
        (by norm_num [cell12799]) (by norm_num [cell12799])
      exact ⟨E.1,E.2.trans (by norm_num [cell12799])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy22 (n := 12799) (by norm_num)
        (q := 1 - (cell12799 ⟨22,by decide⟩).lower)
        (by norm_num [cell12799]) (by norm_num [cell12799])
      exact ⟨E.1,E.2.trans (by norm_num [cell12799])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy23 (n := 12799) (by norm_num)
        (q := 1 - (cell12799 ⟨23,by decide⟩).lower)
        (by norm_num [cell12799]) (by norm_num [cell12799])
      exact ⟨E.1,E.2.trans (by norm_num [cell12799])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy24 (n := 12799) (by norm_num)
        (q := 1 - (cell12799 ⟨24,by decide⟩).lower)
        (by norm_num [cell12799]) (by norm_num [cell12799])
      exact ⟨E.1,E.2.trans (by norm_num [cell12799])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy25 (n := 12799) (by norm_num)
        (q := 1 - (cell12799 ⟨25,by decide⟩).lower)
        (by norm_num [cell12799]) (by norm_num [cell12799])
      exact ⟨E.1,E.2.trans (by norm_num [cell12799])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy26 (n := 12799) (by norm_num)
        (q := 1 - (cell12799 ⟨26,by decide⟩).lower)
        (by norm_num [cell12799]) (by norm_num [cell12799])
      exact ⟨E.1,E.2.trans (by norm_num [cell12799])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy27 (n := 12799) (by norm_num)
        (q := 1 - (cell12799 ⟨27,by decide⟩).lower)
        (by norm_num [cell12799]) (by norm_num [cell12799])
      exact ⟨E.1,E.2.trans (by norm_num [cell12799])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy28 (n := 12799) (by norm_num)
        (q := 1 - (cell12799 ⟨28,by decide⟩).lower)
        (by norm_num [cell12799]) (by norm_num [cell12799])
      exact ⟨E.1,E.2.trans (by norm_num [cell12799])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy29 (n := 12799) (by norm_num)
        (q := 1 - (cell12799 ⟨29,by decide⟩).lower)
        (by norm_num [cell12799]) (by norm_num [cell12799])
      exact ⟨E.1,E.2.trans (by norm_num [cell12799])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy30 (n := 12799) (by norm_num)
        (q := 1 - (cell12799 ⟨30,by decide⟩).lower)
        (by norm_num [cell12799]) (by norm_num [cell12799])
      exact ⟨E.1,E.2.trans (by norm_num [cell12799])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy31 (n := 12799) (by norm_num)
        (q := 1 - (cell12799 ⟨31,by decide⟩).lower)
        (by norm_num [cell12799]) (by norm_num [cell12799])
      exact ⟨E.1,E.2.trans (by norm_num [cell12799])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy32 (n := 12799) (by norm_num)
        (q := 1 - (cell12799 ⟨32,by decide⟩).lower)
        (by norm_num [cell12799]) (by norm_num [cell12799])
      exact ⟨E.1,E.2.trans (by norm_num [cell12799])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy33 (n := 12799) (by norm_num)
        (q := 1 - (cell12799 ⟨33,by decide⟩).lower)
        (by norm_num [cell12799]) (by norm_num [cell12799])
      exact ⟨E.1,E.2.trans (by norm_num [cell12799])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy34 (n := 12799) (by norm_num)
        (q := 1 - (cell12799 ⟨34,by decide⟩).lower)
        (by norm_num [cell12799]) (by norm_num [cell12799])
      exact ⟨E.1,E.2.trans (by norm_num [cell12799])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy35 (n := 12799) (by norm_num)
        (q := 1 - (cell12799 ⟨35,by decide⟩).lower)
        (by norm_num [cell12799]) (by norm_num [cell12799])
      exact ⟨E.1,E.2.trans (by norm_num [cell12799])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy36 (n := 12799) (by norm_num)
        (q := 1 - (cell12799 ⟨36,by decide⟩).lower)
        (by norm_num [cell12799]) (by norm_num [cell12799])
      exact ⟨E.1,E.2.trans (by norm_num [cell12799])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy37 (n := 12799) (by norm_num)
        (q := 1 - (cell12799 ⟨37,by decide⟩).lower)
        (by norm_num [cell12799]) (by norm_num [cell12799])
      exact ⟨E.1,E.2.trans (by norm_num [cell12799])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy38 (n := 12799) (by norm_num)
        (q := 1 - (cell12799 ⟨38,by decide⟩).lower)
        (by norm_num [cell12799]) (by norm_num [cell12799])
      exact ⟨E.1,E.2.trans (by norm_num [cell12799])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy39 (n := 12799) (by norm_num)
        (q := 1 - (cell12799 ⟨39,by decide⟩).lower)
        (by norm_num [cell12799]) (by norm_num [cell12799])
      exact ⟨E.1,E.2.trans (by norm_num [cell12799])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy40 (n := 12799) (by norm_num)
        (q := 1 - (cell12799 ⟨40,by decide⟩).lower)
        (by norm_num [cell12799]) (by norm_num [cell12799])
      exact ⟨E.1,E.2.trans (by norm_num [cell12799])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy41 (n := 12799) (by norm_num)
        (q := 1 - (cell12799 ⟨41,by decide⟩).lower)
        (by norm_num [cell12799]) (by norm_num [cell12799])
      exact ⟨E.1,E.2.trans (by norm_num [cell12799])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy42 (n := 12799) (by norm_num)
        (q := 1 - (cell12799 ⟨42,by decide⟩).lower)
        (by norm_num [cell12799]) (by norm_num [cell12799])
      exact ⟨E.1,E.2.trans (by norm_num [cell12799])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy43 (n := 12799) (by norm_num)
        (q := 1 - (cell12799 ⟨43,by decide⟩).lower)
        (by norm_num [cell12799]) (by norm_num [cell12799])
      exact ⟨E.1,E.2.trans (by norm_num [cell12799])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy44 (n := 12799) (by norm_num)
        (q := 1 - (cell12799 ⟨44,by decide⟩).lower)
        (by norm_num [cell12799]) (by norm_num [cell12799])
      exact ⟨E.1,E.2.trans (by norm_num [cell12799])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy45 (n := 12799) (by norm_num)
        (q := 1 - (cell12799 ⟨45,by decide⟩).lower)
        (by norm_num [cell12799]) (by norm_num [cell12799])
      exact ⟨E.1,E.2.trans (by norm_num [cell12799])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy46 (n := 12799) (by norm_num)
        (q := 1 - (cell12799 ⟨46,by decide⟩).lower)
        (by norm_num [cell12799]) (by norm_num [cell12799])
      exact ⟨E.1,E.2.trans (by norm_num [cell12799])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy47 (n := 12799) (by norm_num)
        (q := 1 - (cell12799 ⟨47,by decide⟩).lower)
        (by norm_num [cell12799]) (by norm_num [cell12799])
      exact ⟨E.1,E.2.trans (by norm_num [cell12799])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy48 (n := 12799) (by norm_num)
        (q := 1 - (cell12799 ⟨48,by decide⟩).lower)
        (by norm_num [cell12799]) (by norm_num [cell12799])
      exact ⟨E.1,E.2.trans (by norm_num [cell12799])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy49 (n := 12799) (by norm_num)
        (q := 1 - (cell12799 ⟨49,by decide⟩).lower)
        (by norm_num [cell12799]) (by norm_num [cell12799])
      exact ⟨E.1,E.2.trans (by norm_num [cell12799])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy50 (n := 12799) (by norm_num)
        (q := 1 - (cell12799 ⟨50,by decide⟩).lower)
        (by norm_num [cell12799]) (by norm_num [cell12799])
      exact ⟨E.1,E.2.trans (by norm_num [cell12799])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy51 (n := 12799) (by norm_num)
        (q := 1 - (cell12799 ⟨51,by decide⟩).lower)
        (by norm_num [cell12799]) (by norm_num [cell12799])
      exact ⟨E.1,E.2.trans (by norm_num [cell12799])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy52 (n := 12799) (by norm_num)
        (q := 1 - (cell12799 ⟨52,by decide⟩).lower)
        (by norm_num [cell12799]) (by norm_num [cell12799])
      exact ⟨E.1,E.2.trans (by norm_num [cell12799])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12799

/-! Source-cell containment and simple scalar guards at 12799. -/
namespace BstLean.Part269.N12799
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12799)
open BstLean.Part268 (cell12799)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12799 ⟨10,by decide⟩).lower ∧ (cell12799 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12799 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12799 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12799 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12799 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12799 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12799,cell12799,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12799 ⟨11,by decide⟩).lower ∧ (cell12799 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12799 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12799 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12799 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12799 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12799 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12799,cell12799,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12799 ⟨12,by decide⟩).lower ∧ (cell12799 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12799 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12799 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12799 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12799 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12799 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12799,cell12799,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12799 ⟨13,by decide⟩).lower ∧ (cell12799 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12799 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12799 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12799 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12799 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12799 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12799,cell12799,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12799 ⟨14,by decide⟩).lower ∧ (cell12799 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12799 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12799 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12799 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12799 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12799 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12799,cell12799,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12799 ⟨15,by decide⟩).lower ∧ (cell12799 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12799 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12799 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12799 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12799 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12799 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12799,cell12799,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12799 ⟨16,by decide⟩).lower ∧ (cell12799 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12799 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12799 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12799 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12799 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12799 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12799,cell12799,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12799 ⟨17,by decide⟩).lower ∧ (cell12799 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12799 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12799 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12799 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12799 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12799 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12799,cell12799,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12799 ⟨18,by decide⟩).lower ∧ (cell12799 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12799 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12799 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12799 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12799 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12799 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12799,cell12799,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12799 ⟨19,by decide⟩).lower ∧ (cell12799 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12799 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12799 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12799 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12799 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12799 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12799,cell12799,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12799 ⟨20,by decide⟩).lower ∧ (cell12799 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12799 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12799 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12799 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12799 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12799 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12799,cell12799,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12799 ⟨21,by decide⟩).lower ∧ (cell12799 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12799 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12799 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12799 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12799 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12799 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12799,cell12799,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12799 ⟨22,by decide⟩).lower ∧ (cell12799 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12799 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12799 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12799 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12799 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12799 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12799,cell12799,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12799 ⟨23,by decide⟩).lower ∧ (cell12799 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12799 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12799 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12799 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12799 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12799 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12799,cell12799,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12799 ⟨24,by decide⟩).lower ∧ (cell12799 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12799 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12799 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12799 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12799 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12799 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12799,cell12799,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12799 ⟨25,by decide⟩).lower ∧ (cell12799 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12799 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12799 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12799 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12799 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12799 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12799,cell12799,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12799 ⟨26,by decide⟩).lower ∧ (cell12799 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12799 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12799 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12799 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12799 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12799 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12799,cell12799,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12799 ⟨27,by decide⟩).lower ∧ (cell12799 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12799 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12799 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12799 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12799 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12799 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12799,cell12799,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12799 ⟨28,by decide⟩).lower ∧ (cell12799 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12799 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12799 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12799 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12799 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12799 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12799,cell12799,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12799 ⟨29,by decide⟩).lower ∧ (cell12799 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12799 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12799 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12799 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12799 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12799 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12799,cell12799,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12799 ⟨30,by decide⟩).lower ∧ (cell12799 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12799 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12799 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12799 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12799 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12799 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12799,cell12799,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12799 ⟨31,by decide⟩).lower ∧ (cell12799 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12799 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12799 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12799 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12799 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12799 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12799,cell12799,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12799 ⟨32,by decide⟩).lower ∧ (cell12799 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12799 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12799 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12799 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12799 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12799 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12799,cell12799,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12799 ⟨33,by decide⟩).lower ∧ (cell12799 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12799 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12799 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12799 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12799 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12799 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12799,cell12799,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12799 ⟨34,by decide⟩).lower ∧ (cell12799 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12799 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12799 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12799 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12799 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12799 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12799,cell12799,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12799 ⟨35,by decide⟩).lower ∧ (cell12799 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12799 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12799 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12799 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12799 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12799 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12799,cell12799,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12799 ⟨36,by decide⟩).lower ∧ (cell12799 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12799 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12799 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12799 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12799 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12799 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12799,cell12799,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12799 ⟨37,by decide⟩).lower ∧ (cell12799 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12799 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12799 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12799 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12799 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12799 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12799,cell12799,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12799 ⟨38,by decide⟩).lower ∧ (cell12799 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12799 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12799 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12799 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12799 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12799 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12799,cell12799,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12799 ⟨39,by decide⟩).lower ∧ (cell12799 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12799 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12799 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12799 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12799 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12799 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12799,cell12799,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12799 ⟨40,by decide⟩).lower ∧ (cell12799 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12799 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12799 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12799 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12799 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12799 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12799,cell12799,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12799 ⟨41,by decide⟩).lower ∧ (cell12799 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12799 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12799 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12799 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12799 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12799 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12799,cell12799,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12799 ⟨42,by decide⟩).lower ∧ (cell12799 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12799 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12799 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12799 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12799 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12799 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12799,cell12799,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12799 ⟨43,by decide⟩).lower ∧ (cell12799 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12799 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12799 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12799 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12799 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12799 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12799,cell12799,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12799 ⟨44,by decide⟩).lower ∧ (cell12799 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12799 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12799 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12799 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12799 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12799 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12799,cell12799,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12799 ⟨45,by decide⟩).lower ∧ (cell12799 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12799 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12799 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12799 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12799 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12799 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12799,cell12799,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12799 ⟨46,by decide⟩).lower ∧ (cell12799 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12799 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12799 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12799 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12799 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12799 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12799,cell12799,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12799 ⟨47,by decide⟩).lower ∧ (cell12799 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12799 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12799 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12799 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12799 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12799 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12799,cell12799,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12799 ⟨48,by decide⟩).lower ∧ (cell12799 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12799 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12799 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12799 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12799 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12799 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12799,cell12799,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12799 ⟨49,by decide⟩).lower ∧ (cell12799 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12799 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12799 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12799 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12799 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12799 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12799,cell12799,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12799 ⟨50,by decide⟩).lower ∧ (cell12799 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12799 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12799 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12799 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12799 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12799 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12799,cell12799,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12799 ⟨51,by decide⟩).lower ∧ (cell12799 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12799 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12799 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12799 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12799 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12799 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12799,cell12799,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12799 ⟨52,by decide⟩).lower ∧ (cell12799 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12799 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12799 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12799 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12799 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12799 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12799,cell12799,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12799 i).lower ∧
    (cell12799 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12799 i).upper ≤ (0.532 : ℝ) ∧
    (cell12799 i).centre ≤ (0.1 : ℝ) ∧ (cell12799 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12799 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12799 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12799

/-! The local source numeric instances at 12799 have no network premises. -/
namespace BstLean.Part269.N12799
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12799)
open BstLean.Part268 (cell12799)

noncomputable def sourceNumerics12799 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12799 (cell12799 i)
      scalarRow12799.M scalarRow12799.H scalarRow12799.xi := by
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
    energy_allowance := scalarRow12799.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12799]
    centre_nonneg := (scalarRow12799.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D17.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12799])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12799