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
import BstLean.Part269Direction13
import BstLean.Part269Shared13
import BstLean.Part269Finite
import BstLean.Part269Rows13
import BstLean.Part269Source
/-! Actual 12688 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12688
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12688 ≤ (1.035826299724 : ℝ) := by
  have hr : (112.641022722629 : ℝ) ≤ √(12688 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.641022722629 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12688 12688 (11 / 1000) ≤
    (0.008486135952 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12688) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.641022722629 : ℝ) ≤ √(12688 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12688)
  have hdiv : K / √(12688 : ℝ) ≤ K / 112.641022722629 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.641022722629 ≤ (0.008486135952 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12688.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12688 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12688 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12688 := gPlus_lower 12688
end BstLean.Part269.N12688

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12688
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035826299723 : ℝ) ≤ wn 12688 := by
  have hn : √(12688 : ℝ) ≤ 112.641022722630 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12688 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.641022722630 ≤ 2 / √(12688 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000252123249 : ℝ) ≤ rhoBar 12688 BstLean.Part154.csC ∧
    rhoBar 12688 BstLean.Part154.csC ≤ 0.000252123639 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035826299723 : ℝ) / (1.295212 * 12688) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035826299724 : ℝ) / (1.29521 * 12688) := by gcongr
      _ ≤ (0.000252123639 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12688 BstLean.Part154.csC) ≤ 0.001008558123 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12688 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12688 BstLean.Part154.csC) (piBar (rhoBar 12688 BstLean.Part154.csC)) ≤ 0.000192573745 ∧
    cc1 (rhoBar 12688 BstLean.Part154.csC) (piBar (rhoBar 12688 BstLean.Part154.csC)) ≤ 0.000122535951 ∧
    cc2 (rhoBar 12688 BstLean.Part154.csC) ≤ 0.000071133056 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12688 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12688 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12688 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12688 BstLean.Part154.csC * nuR (rhoBar 12688 BstLean.Part154.csC)) ≤ 0.000504263170 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000252123639 : ℝ) * 0.001008558123 := by gcongr
      _ ≤ (0.000504263170 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12688 BstLean.Part154.csC) * nuR (rhoBar 12688 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001008558123 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12688 BstLean.Part154.csC) * rhoBar 12688 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000252123639 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000252123639 / 2 + 0.399 * 0.001008558123 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000192573745 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000504263170 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122535951 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000252123639 / 1.414213562 := by gcongr
      _ ≤ (0.000071133056 : ℝ) := by norm_num

end BstLean.Part269.N12688

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12688
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12688 BstLean.Part154.csC) (piBar (rhoBar 12688 BstLean.Part154.csC)) ≤ 1.60151E-7 := by
  have hr0 : 0 ≤ rhoBar 12688 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12688 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12688 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12688 BstLean.Part154.csC) (piBar (rhoBar 12688 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12688 BstLean.Part154.csC) (piBar (rhoBar 12688 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12688 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000192573745 : ℝ) ^ 2 + 0.000122535951 ^ 2 + 3 * 0.000071133056 ^ 2 +
        2 * 0.797885 * 0.000192573745 * 0.000122535951 + 2 * 0.000192573745 * 0.000071133056 +
        4 * 0.797885 * 0.000122535951 * 0.000071133056 := by gcongr
    _ ≤ (1.60151E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12688 BstLean.Part154.csC Θ ≤ 0.002631865461 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12688 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12688 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12688 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12688 BstLean.Part154.csC) (piBar (rhoBar 12688 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12688 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035826299724 * 1.60151E-7 / (0.000252123249 : ℝ) := by gcongr
    _ ≤ 0.002631865461 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12688 BstLean.Part154.csC Θ ≤ 0.002920241779 + 0.000665029186 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12688 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12688 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12688 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035826299724 : ℝ) * ((2 * Θ * 0.000252123639 +
        (6863 / 10000) * 0.000252123639 * 12688 * 0.001008558123) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002920241779 + 0.000665029186 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12688 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12688 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12688 0.011 Θ ∧ gammaRatio 12688 0.011 Θ ≤ 0.000086673588 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12688 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035826299724 : ℝ) * 0.525 / ((1 - 0.011) * 12688) := by gcongr
      _ ≤ (0.000086673588 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12688 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12688 0.011 Θ) :=
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
    badAllowance 12688 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000615501984 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12688 BstLean.Part154.csC) 1.22 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 2 (rhoBar 12688 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12688 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12688 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12688 0.011 Θ) 1.12 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 1 (gammaRatio 12688 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12688 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12688 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12688 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12688 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035826299724 : ℝ) * 12688 *
        (2.2721E-8 / 1.1045361 + 2.7751E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000615501984 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12688 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003535743763 + 0.003296894647 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12688

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12688
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12688 BstLean.Part154.csC) (piBar (rhoBar 12688 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12688 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12688 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12688 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12688 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12688 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12688 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12688 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12688 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12688 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12688 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12688 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12688 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12688 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12688 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052509395312 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12688) ≤ 0.010602154990 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12688 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035826299724)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010602154990 + 2 * 0.737676 / 12688) := by gcongr
    _ ≤ (0.052509395312 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12688 12 ≤ 0.0015 := by
  exact BstLean.Part269.S13.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12688

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12688
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560503025102 : ℝ) ≤ plow 12688 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12688) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052773213453)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001381729368) : eMP 12688 0.011 xi bn ≤ 0.001189521978 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12688 : ℝ) * (1 - 0.011))) ≤ 0.000588154906 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001381729368 / (12688 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000588154906 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000588154906 : ℝ) + 3.141593 * 0.052773213453 / (12688 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001189521978 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052773213453)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001381729368) : PiBarMP 12688 12 0.011 xi bn ≤ 0.161328019162 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12688 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037171620466 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.019783966940 : ℝ) ≤ √((12688 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.641022722629 : ℝ) ≤ √(12688 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12688) ≤ 0.123688580999 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037171620466 + 0.052773213453 * 1.772454 / (2 * (112.019783966940 : ℝ))) * (1 + 0.001189521978) +
        8 / (12688 * 112.641022722629) + 0.123688580999 := by gcongr
    _ ≤ (0.161328019162 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052773213453)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001381729368) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282233607038) :
    parallelOracle 12688 0.011 xi bn cd ≤ 0.162319440249 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12688 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12688 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560503025102 : ℝ) ≤ plow 12688 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.641022722629 : ℝ) ≤ √(12688 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282233607038 : ℝ) / (2 * 0.560503025102 * 112.641022722629)) * 0.161328019162 +
        0.282233607038 ^ 2 / (2 * 0.560503025102 * 112.641022722629) := by gcongr
    _ ≤ (0.162319440249 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052773213453) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001381729368)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282233607038) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12688 12688 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560503025102 : ℝ) ≤ plow 12688 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.641022722629 : ℝ) ≤ √(12688 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12688 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12688 Θ 1.22 ≤ 0.011772802377 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.641022722629 := by gcongr <;> linarith
      _ ≤ (0.011772802377 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12688 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12688 12688 0.011 ≤ 0.008486135952 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12688 12688 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12688 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12688 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12688 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12688 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162319440249 + 0.011772802377 + (0.008486135952 : ℝ) *
        (1 + 2 * (0.282233607038 + 0.011772802377) / (0.560503025102 * 112.641022722629))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12688]

end BstLean.Part269.N12688

/-! The original eight local profiles supply actual 12688 moment certificates. -/
namespace BstLean.Part269.N12688
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12688 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12688 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12688 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052773213453 ∧
    0 ≤ bN 12688 BstLean.Part154.csC (groupTheta g) ∧ bN 12688 BstLean.Part154.csC (groupTheta g) ≤ 0.001381729368 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12688 12688 0.011
      (momentAllowance 12688 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12688 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12688 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12688 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12688 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12688 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229724211726 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12688 0.011
      (momentAllowance 12688 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12688 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12688
/-! The actual computed-centre upper energy formula at 12688. -/
namespace BstLean.Part269.N12688
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12688

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12688
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12688)
open BstLean.Part268 (cell12688)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085525330107
  | 2 => 0.086468725535
  | 3 => 0.087410355142
  | 4 => 0.088351658751
  | 5 => 0.089294377183
  | 6 => 0.090240596874
  | 7 => 0.091192798669
  | 8 => 0.092153910833
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12688 12688 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12688 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003538895953 + 0.003300387184 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S13.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12688

/-! Actual upper energy certificates on all 43 source endpoints at 12688. -/
namespace BstLean.Part269.N12688
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12688)
open BstLean.Part268 (cell12688)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12688 (gMinus 12688) (1 - (cell12688 i).lower) ≤ 1 ∧
    energyUpper 12688 (gMinus 12688) (BstLean.Part211.gPlus 12688)
      (finiteEnergy 12688 12688 0.011) (1 - (cell12688 i).lower) ≤
      (cell12688 i).energy := by
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
      have E := BstLean.Part269.S13.uniformEnergy10 (n := 12688) (by norm_num)
        (q := 1 - (cell12688 ⟨10,by decide⟩).lower)
        (by norm_num [cell12688]) (by norm_num [cell12688])
      exact ⟨E.1,E.2.trans (by norm_num [cell12688])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy11 (n := 12688) (by norm_num)
        (q := 1 - (cell12688 ⟨11,by decide⟩).lower)
        (by norm_num [cell12688]) (by norm_num [cell12688])
      exact ⟨E.1,E.2.trans (by norm_num [cell12688])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy12 (n := 12688) (by norm_num)
        (q := 1 - (cell12688 ⟨12,by decide⟩).lower)
        (by norm_num [cell12688]) (by norm_num [cell12688])
      exact ⟨E.1,E.2.trans (by norm_num [cell12688])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy13 (n := 12688) (by norm_num)
        (q := 1 - (cell12688 ⟨13,by decide⟩).lower)
        (by norm_num [cell12688]) (by norm_num [cell12688])
      exact ⟨E.1,E.2.trans (by norm_num [cell12688])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy14 (n := 12688) (by norm_num)
        (q := 1 - (cell12688 ⟨14,by decide⟩).lower)
        (by norm_num [cell12688]) (by norm_num [cell12688])
      exact ⟨E.1,E.2.trans (by norm_num [cell12688])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy15 (n := 12688) (by norm_num)
        (q := 1 - (cell12688 ⟨15,by decide⟩).lower)
        (by norm_num [cell12688]) (by norm_num [cell12688])
      exact ⟨E.1,E.2.trans (by norm_num [cell12688])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy16 (n := 12688) (by norm_num)
        (q := 1 - (cell12688 ⟨16,by decide⟩).lower)
        (by norm_num [cell12688]) (by norm_num [cell12688])
      exact ⟨E.1,E.2.trans (by norm_num [cell12688])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy17 (n := 12688) (by norm_num)
        (q := 1 - (cell12688 ⟨17,by decide⟩).lower)
        (by norm_num [cell12688]) (by norm_num [cell12688])
      exact ⟨E.1,E.2.trans (by norm_num [cell12688])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy18 (n := 12688) (by norm_num)
        (q := 1 - (cell12688 ⟨18,by decide⟩).lower)
        (by norm_num [cell12688]) (by norm_num [cell12688])
      exact ⟨E.1,E.2.trans (by norm_num [cell12688])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy19 (n := 12688) (by norm_num)
        (q := 1 - (cell12688 ⟨19,by decide⟩).lower)
        (by norm_num [cell12688]) (by norm_num [cell12688])
      exact ⟨E.1,E.2.trans (by norm_num [cell12688])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy20 (n := 12688) (by norm_num)
        (q := 1 - (cell12688 ⟨20,by decide⟩).lower)
        (by norm_num [cell12688]) (by norm_num [cell12688])
      exact ⟨E.1,E.2.trans (by norm_num [cell12688])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy21 (n := 12688) (by norm_num)
        (q := 1 - (cell12688 ⟨21,by decide⟩).lower)
        (by norm_num [cell12688]) (by norm_num [cell12688])
      exact ⟨E.1,E.2.trans (by norm_num [cell12688])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy22 (n := 12688) (by norm_num)
        (q := 1 - (cell12688 ⟨22,by decide⟩).lower)
        (by norm_num [cell12688]) (by norm_num [cell12688])
      exact ⟨E.1,E.2.trans (by norm_num [cell12688])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy23 (n := 12688) (by norm_num)
        (q := 1 - (cell12688 ⟨23,by decide⟩).lower)
        (by norm_num [cell12688]) (by norm_num [cell12688])
      exact ⟨E.1,E.2.trans (by norm_num [cell12688])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy24 (n := 12688) (by norm_num)
        (q := 1 - (cell12688 ⟨24,by decide⟩).lower)
        (by norm_num [cell12688]) (by norm_num [cell12688])
      exact ⟨E.1,E.2.trans (by norm_num [cell12688])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy25 (n := 12688) (by norm_num)
        (q := 1 - (cell12688 ⟨25,by decide⟩).lower)
        (by norm_num [cell12688]) (by norm_num [cell12688])
      exact ⟨E.1,E.2.trans (by norm_num [cell12688])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy26 (n := 12688) (by norm_num)
        (q := 1 - (cell12688 ⟨26,by decide⟩).lower)
        (by norm_num [cell12688]) (by norm_num [cell12688])
      exact ⟨E.1,E.2.trans (by norm_num [cell12688])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy27 (n := 12688) (by norm_num)
        (q := 1 - (cell12688 ⟨27,by decide⟩).lower)
        (by norm_num [cell12688]) (by norm_num [cell12688])
      exact ⟨E.1,E.2.trans (by norm_num [cell12688])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy28 (n := 12688) (by norm_num)
        (q := 1 - (cell12688 ⟨28,by decide⟩).lower)
        (by norm_num [cell12688]) (by norm_num [cell12688])
      exact ⟨E.1,E.2.trans (by norm_num [cell12688])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy29 (n := 12688) (by norm_num)
        (q := 1 - (cell12688 ⟨29,by decide⟩).lower)
        (by norm_num [cell12688]) (by norm_num [cell12688])
      exact ⟨E.1,E.2.trans (by norm_num [cell12688])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy30 (n := 12688) (by norm_num)
        (q := 1 - (cell12688 ⟨30,by decide⟩).lower)
        (by norm_num [cell12688]) (by norm_num [cell12688])
      exact ⟨E.1,E.2.trans (by norm_num [cell12688])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy31 (n := 12688) (by norm_num)
        (q := 1 - (cell12688 ⟨31,by decide⟩).lower)
        (by norm_num [cell12688]) (by norm_num [cell12688])
      exact ⟨E.1,E.2.trans (by norm_num [cell12688])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy32 (n := 12688) (by norm_num)
        (q := 1 - (cell12688 ⟨32,by decide⟩).lower)
        (by norm_num [cell12688]) (by norm_num [cell12688])
      exact ⟨E.1,E.2.trans (by norm_num [cell12688])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy33 (n := 12688) (by norm_num)
        (q := 1 - (cell12688 ⟨33,by decide⟩).lower)
        (by norm_num [cell12688]) (by norm_num [cell12688])
      exact ⟨E.1,E.2.trans (by norm_num [cell12688])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy34 (n := 12688) (by norm_num)
        (q := 1 - (cell12688 ⟨34,by decide⟩).lower)
        (by norm_num [cell12688]) (by norm_num [cell12688])
      exact ⟨E.1,E.2.trans (by norm_num [cell12688])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy35 (n := 12688) (by norm_num)
        (q := 1 - (cell12688 ⟨35,by decide⟩).lower)
        (by norm_num [cell12688]) (by norm_num [cell12688])
      exact ⟨E.1,E.2.trans (by norm_num [cell12688])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy36 (n := 12688) (by norm_num)
        (q := 1 - (cell12688 ⟨36,by decide⟩).lower)
        (by norm_num [cell12688]) (by norm_num [cell12688])
      exact ⟨E.1,E.2.trans (by norm_num [cell12688])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy37 (n := 12688) (by norm_num)
        (q := 1 - (cell12688 ⟨37,by decide⟩).lower)
        (by norm_num [cell12688]) (by norm_num [cell12688])
      exact ⟨E.1,E.2.trans (by norm_num [cell12688])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy38 (n := 12688) (by norm_num)
        (q := 1 - (cell12688 ⟨38,by decide⟩).lower)
        (by norm_num [cell12688]) (by norm_num [cell12688])
      exact ⟨E.1,E.2.trans (by norm_num [cell12688])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy39 (n := 12688) (by norm_num)
        (q := 1 - (cell12688 ⟨39,by decide⟩).lower)
        (by norm_num [cell12688]) (by norm_num [cell12688])
      exact ⟨E.1,E.2.trans (by norm_num [cell12688])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy40 (n := 12688) (by norm_num)
        (q := 1 - (cell12688 ⟨40,by decide⟩).lower)
        (by norm_num [cell12688]) (by norm_num [cell12688])
      exact ⟨E.1,E.2.trans (by norm_num [cell12688])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy41 (n := 12688) (by norm_num)
        (q := 1 - (cell12688 ⟨41,by decide⟩).lower)
        (by norm_num [cell12688]) (by norm_num [cell12688])
      exact ⟨E.1,E.2.trans (by norm_num [cell12688])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy42 (n := 12688) (by norm_num)
        (q := 1 - (cell12688 ⟨42,by decide⟩).lower)
        (by norm_num [cell12688]) (by norm_num [cell12688])
      exact ⟨E.1,E.2.trans (by norm_num [cell12688])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy43 (n := 12688) (by norm_num)
        (q := 1 - (cell12688 ⟨43,by decide⟩).lower)
        (by norm_num [cell12688]) (by norm_num [cell12688])
      exact ⟨E.1,E.2.trans (by norm_num [cell12688])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy44 (n := 12688) (by norm_num)
        (q := 1 - (cell12688 ⟨44,by decide⟩).lower)
        (by norm_num [cell12688]) (by norm_num [cell12688])
      exact ⟨E.1,E.2.trans (by norm_num [cell12688])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy45 (n := 12688) (by norm_num)
        (q := 1 - (cell12688 ⟨45,by decide⟩).lower)
        (by norm_num [cell12688]) (by norm_num [cell12688])
      exact ⟨E.1,E.2.trans (by norm_num [cell12688])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy46 (n := 12688) (by norm_num)
        (q := 1 - (cell12688 ⟨46,by decide⟩).lower)
        (by norm_num [cell12688]) (by norm_num [cell12688])
      exact ⟨E.1,E.2.trans (by norm_num [cell12688])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy47 (n := 12688) (by norm_num)
        (q := 1 - (cell12688 ⟨47,by decide⟩).lower)
        (by norm_num [cell12688]) (by norm_num [cell12688])
      exact ⟨E.1,E.2.trans (by norm_num [cell12688])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy48 (n := 12688) (by norm_num)
        (q := 1 - (cell12688 ⟨48,by decide⟩).lower)
        (by norm_num [cell12688]) (by norm_num [cell12688])
      exact ⟨E.1,E.2.trans (by norm_num [cell12688])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy49 (n := 12688) (by norm_num)
        (q := 1 - (cell12688 ⟨49,by decide⟩).lower)
        (by norm_num [cell12688]) (by norm_num [cell12688])
      exact ⟨E.1,E.2.trans (by norm_num [cell12688])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy50 (n := 12688) (by norm_num)
        (q := 1 - (cell12688 ⟨50,by decide⟩).lower)
        (by norm_num [cell12688]) (by norm_num [cell12688])
      exact ⟨E.1,E.2.trans (by norm_num [cell12688])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy51 (n := 12688) (by norm_num)
        (q := 1 - (cell12688 ⟨51,by decide⟩).lower)
        (by norm_num [cell12688]) (by norm_num [cell12688])
      exact ⟨E.1,E.2.trans (by norm_num [cell12688])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy52 (n := 12688) (by norm_num)
        (q := 1 - (cell12688 ⟨52,by decide⟩).lower)
        (by norm_num [cell12688]) (by norm_num [cell12688])
      exact ⟨E.1,E.2.trans (by norm_num [cell12688])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12688

/-! Source-cell containment and simple scalar guards at 12688. -/
namespace BstLean.Part269.N12688
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12688)
open BstLean.Part268 (cell12688)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12688 ⟨10,by decide⟩).lower ∧ (cell12688 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12688 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12688 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12688 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12688 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12688 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12688,cell12688,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12688 ⟨11,by decide⟩).lower ∧ (cell12688 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12688 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12688 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12688 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12688 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12688 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12688,cell12688,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12688 ⟨12,by decide⟩).lower ∧ (cell12688 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12688 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12688 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12688 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12688 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12688 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12688,cell12688,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12688 ⟨13,by decide⟩).lower ∧ (cell12688 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12688 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12688 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12688 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12688 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12688 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12688,cell12688,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12688 ⟨14,by decide⟩).lower ∧ (cell12688 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12688 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12688 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12688 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12688 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12688 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12688,cell12688,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12688 ⟨15,by decide⟩).lower ∧ (cell12688 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12688 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12688 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12688 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12688 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12688 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12688,cell12688,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12688 ⟨16,by decide⟩).lower ∧ (cell12688 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12688 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12688 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12688 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12688 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12688 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12688,cell12688,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12688 ⟨17,by decide⟩).lower ∧ (cell12688 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12688 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12688 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12688 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12688 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12688 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12688,cell12688,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12688 ⟨18,by decide⟩).lower ∧ (cell12688 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12688 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12688 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12688 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12688 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12688 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12688,cell12688,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12688 ⟨19,by decide⟩).lower ∧ (cell12688 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12688 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12688 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12688 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12688 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12688 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12688,cell12688,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12688 ⟨20,by decide⟩).lower ∧ (cell12688 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12688 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12688 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12688 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12688 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12688 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12688,cell12688,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12688 ⟨21,by decide⟩).lower ∧ (cell12688 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12688 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12688 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12688 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12688 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12688 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12688,cell12688,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12688 ⟨22,by decide⟩).lower ∧ (cell12688 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12688 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12688 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12688 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12688 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12688 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12688,cell12688,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12688 ⟨23,by decide⟩).lower ∧ (cell12688 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12688 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12688 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12688 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12688 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12688 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12688,cell12688,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12688 ⟨24,by decide⟩).lower ∧ (cell12688 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12688 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12688 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12688 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12688 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12688 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12688,cell12688,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12688 ⟨25,by decide⟩).lower ∧ (cell12688 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12688 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12688 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12688 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12688 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12688 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12688,cell12688,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12688 ⟨26,by decide⟩).lower ∧ (cell12688 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12688 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12688 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12688 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12688 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12688 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12688,cell12688,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12688 ⟨27,by decide⟩).lower ∧ (cell12688 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12688 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12688 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12688 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12688 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12688 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12688,cell12688,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12688 ⟨28,by decide⟩).lower ∧ (cell12688 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12688 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12688 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12688 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12688 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12688 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12688,cell12688,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12688 ⟨29,by decide⟩).lower ∧ (cell12688 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12688 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12688 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12688 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12688 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12688 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12688,cell12688,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12688 ⟨30,by decide⟩).lower ∧ (cell12688 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12688 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12688 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12688 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12688 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12688 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12688,cell12688,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12688 ⟨31,by decide⟩).lower ∧ (cell12688 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12688 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12688 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12688 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12688 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12688 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12688,cell12688,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12688 ⟨32,by decide⟩).lower ∧ (cell12688 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12688 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12688 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12688 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12688 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12688 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12688,cell12688,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12688 ⟨33,by decide⟩).lower ∧ (cell12688 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12688 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12688 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12688 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12688 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12688 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12688,cell12688,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12688 ⟨34,by decide⟩).lower ∧ (cell12688 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12688 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12688 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12688 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12688 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12688 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12688,cell12688,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12688 ⟨35,by decide⟩).lower ∧ (cell12688 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12688 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12688 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12688 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12688 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12688 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12688,cell12688,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12688 ⟨36,by decide⟩).lower ∧ (cell12688 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12688 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12688 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12688 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12688 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12688 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12688,cell12688,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12688 ⟨37,by decide⟩).lower ∧ (cell12688 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12688 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12688 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12688 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12688 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12688 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12688,cell12688,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12688 ⟨38,by decide⟩).lower ∧ (cell12688 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12688 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12688 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12688 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12688 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12688 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12688,cell12688,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12688 ⟨39,by decide⟩).lower ∧ (cell12688 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12688 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12688 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12688 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12688 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12688 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12688,cell12688,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12688 ⟨40,by decide⟩).lower ∧ (cell12688 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12688 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12688 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12688 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12688 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12688 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12688,cell12688,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12688 ⟨41,by decide⟩).lower ∧ (cell12688 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12688 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12688 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12688 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12688 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12688 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12688,cell12688,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12688 ⟨42,by decide⟩).lower ∧ (cell12688 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12688 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12688 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12688 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12688 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12688 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12688,cell12688,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12688 ⟨43,by decide⟩).lower ∧ (cell12688 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12688 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12688 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12688 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12688 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12688 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12688,cell12688,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12688 ⟨44,by decide⟩).lower ∧ (cell12688 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12688 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12688 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12688 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12688 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12688 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12688,cell12688,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12688 ⟨45,by decide⟩).lower ∧ (cell12688 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12688 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12688 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12688 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12688 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12688 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12688,cell12688,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12688 ⟨46,by decide⟩).lower ∧ (cell12688 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12688 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12688 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12688 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12688 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12688 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12688,cell12688,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12688 ⟨47,by decide⟩).lower ∧ (cell12688 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12688 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12688 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12688 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12688 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12688 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12688,cell12688,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12688 ⟨48,by decide⟩).lower ∧ (cell12688 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12688 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12688 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12688 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12688 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12688 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12688,cell12688,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12688 ⟨49,by decide⟩).lower ∧ (cell12688 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12688 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12688 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12688 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12688 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12688 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12688,cell12688,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12688 ⟨50,by decide⟩).lower ∧ (cell12688 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12688 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12688 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12688 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12688 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12688 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12688,cell12688,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12688 ⟨51,by decide⟩).lower ∧ (cell12688 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12688 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12688 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12688 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12688 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12688 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12688,cell12688,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12688 ⟨52,by decide⟩).lower ∧ (cell12688 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12688 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12688 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12688 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12688 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12688 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12688,cell12688,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12688 i).lower ∧
    (cell12688 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12688 i).upper ≤ (0.532 : ℝ) ∧
    (cell12688 i).centre ≤ (0.1 : ℝ) ∧ (cell12688 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12688 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12688 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12688

/-! The local source numeric instances at 12688 have no network premises. -/
namespace BstLean.Part269.N12688
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12688)
open BstLean.Part268 (cell12688)

noncomputable def sourceNumerics12688 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12688 (cell12688 i)
      scalarRow12688.M scalarRow12688.H scalarRow12688.xi := by
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
    energy_allowance := scalarRow12688.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12688]
    centre_nonneg := (scalarRow12688.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D13.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12688])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12688
/-! Actual 12689 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12689
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12689 ≤ (1.035824875567 : ℝ) := by
  have hr : (112.645461515322 : ℝ) ≤ √(12689 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.645461515322 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12689 12689 (11 / 1000) ≤
    (0.008485801553 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12689) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.645461515322 : ℝ) ≤ √(12689 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12689)
  have hdiv : K / √(12689 : ℝ) ≤ K / 112.645461515322 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.645461515322 ≤ (0.008485801553 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12689.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12689 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12689 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12689 := gPlus_lower 12689
end BstLean.Part269.N12689

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12689
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035824875566 : ℝ) ≤ wn 12689 := by
  have hn : √(12689 : ℝ) ≤ 112.645461515323 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12689 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.645461515323 ≤ 2 / √(12689 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000252103033 : ℝ) ≤ rhoBar 12689 BstLean.Part154.csC ∧
    rhoBar 12689 BstLean.Part154.csC ≤ 0.000252103423 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035824875566 : ℝ) / (1.295212 * 12689) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035824875567 : ℝ) / (1.29521 * 12689) := by gcongr
      _ ≤ (0.000252103423 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12689 BstLean.Part154.csC) ≤ 0.001008477249 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12689 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12689 BstLean.Part154.csC) (piBar (rhoBar 12689 BstLean.Part154.csC)) ≤ 0.000192558303 ∧
    cc1 (rhoBar 12689 BstLean.Part154.csC) (piBar (rhoBar 12689 BstLean.Part154.csC)) ≤ 0.000122526125 ∧
    cc2 (rhoBar 12689 BstLean.Part154.csC) ≤ 0.000071127352 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12689 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12689 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12689 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12689 BstLean.Part154.csC * nuR (rhoBar 12689 BstLean.Part154.csC)) ≤ 0.000504222735 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000252103423 : ℝ) * 0.001008477249 := by gcongr
      _ ≤ (0.000504222735 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12689 BstLean.Part154.csC) * nuR (rhoBar 12689 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001008477249 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12689 BstLean.Part154.csC) * rhoBar 12689 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000252103423 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000252103423 / 2 + 0.399 * 0.001008477249 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000192558303 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000504222735 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122526125 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000252103423 / 1.414213562 := by gcongr
      _ ≤ (0.000071127352 : ℝ) := by norm_num

end BstLean.Part269.N12689

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12689
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12689 BstLean.Part154.csC) (piBar (rhoBar 12689 BstLean.Part154.csC)) ≤ 1.60125E-7 := by
  have hr0 : 0 ≤ rhoBar 12689 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12689 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12689 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12689 BstLean.Part154.csC) (piBar (rhoBar 12689 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12689 BstLean.Part154.csC) (piBar (rhoBar 12689 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12689 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000192558303 : ℝ) ^ 2 + 0.000122526125 ^ 2 + 3 * 0.000071127352 ^ 2 +
        2 * 0.797885 * 0.000192558303 * 0.000122526125 + 2 * 0.000192558303 * 0.000071127352 +
        4 * 0.797885 * 0.000122526125 * 0.000071127352 := by gcongr
    _ ≤ (1.60125E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12689 BstLean.Part154.csC Θ ≤ 0.002631645582 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12689 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12689 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12689 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12689 BstLean.Part154.csC) (piBar (rhoBar 12689 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12689 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035824875567 * 1.60125E-7 / (0.000252103033 : ℝ) := by gcongr
    _ ≤ 0.002631645582 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12689 BstLean.Part154.csC Θ ≤ 0.002919999583 + 0.000664974948 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12689 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12689 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12689 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035824875567 : ℝ) * ((2 * Θ * 0.000252103423 +
        (6863 / 10000) * 0.000252103423 * 12689 * 0.001008477249) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002919999583 + 0.000664974948 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12689 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12689 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12689 0.011 Θ ∧ gammaRatio 12689 0.011 Θ ≤ 0.000086666638 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12689 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035824875567 : ℝ) * 0.525 / ((1 - 0.011) * 12689) := by gcongr
      _ ≤ (0.000086666638 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12689 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12689 0.011 Θ) :=
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
    badAllowance 12689 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000615501984 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12689 BstLean.Part154.csC) 1.22 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 2 (rhoBar 12689 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12689 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12689 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12689 0.011 Θ) 1.12 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 1 (gammaRatio 12689 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12689 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12689 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12689 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12689 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035824875567 : ℝ) * 12689 *
        (2.2721E-8 / 1.1045361 + 2.7751E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000615501984 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12689 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003535501567 + 0.003296620530 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12689

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12689
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12689 BstLean.Part154.csC) (piBar (rhoBar 12689 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12689 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12689 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12689 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12689 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12689 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12689 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12689 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12689 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12689 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12689 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12689 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12689 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12689 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12689 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052507303733 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12689) ≤ 0.010601737212 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12689 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035824875567)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010601737212 + 2 * 0.737676 / 12689) := by gcongr
    _ ≤ (0.052507303733 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12689 12 ≤ 0.0015 := by
  exact BstLean.Part269.S13.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12689

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12689
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560503070407 : ℝ) ≤ plow 12689 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12689) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052772827346)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001381613931) : eMP 12689 0.011 xi bn ≤ 0.001189425352 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12689 : ℝ) * (1 - 0.011))) ≤ 0.000588107162 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001381613931 / (12689 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000588107162 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000588107162 : ℝ) + 3.141593 * 0.052772827346 / (12689 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001189425352 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052772827346)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001381613931) : PiBarMP 12689 12 0.011 xi bn ≤ 0.161321566755 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12689 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037170067676 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.024198278764 : ℝ) ≤ √((12689 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.645461515322 : ℝ) ≤ √(12689 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12689) ≤ 0.123683707052 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037170067676 + 0.052772827346 * 1.772454 / (2 * (112.024198278764 : ℝ))) * (1 + 0.001189425352) +
        8 / (12689 * 112.645461515322) + 0.123683707052 := by gcongr
    _ ≤ (0.161321566755 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052772827346)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001381613931) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282230675087) :
    parallelOracle 12689 0.011 xi bn cd ≤ 0.162312917422 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12689 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12689 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560503070407 : ℝ) ≤ plow 12689 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.645461515322 : ℝ) ≤ √(12689 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282230675087 : ℝ) / (2 * 0.560503070407 * 112.645461515322)) * 0.161321566755 +
        0.282230675087 ^ 2 / (2 * 0.560503070407 * 112.645461515322) := by gcongr
    _ ≤ (0.162312917422 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052772827346) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001381613931)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282230675087) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12689 12689 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560503070407 : ℝ) ≤ plow 12689 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.645461515322 : ℝ) ≤ √(12689 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12689 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12689 Θ 1.22 ≤ 0.011772338470 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.645461515322 := by gcongr <;> linarith
      _ ≤ (0.011772338470 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12689 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12689 12689 0.011 ≤ 0.008485801553 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12689 12689 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12689 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12689 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12689 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12689 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162312917422 + 0.011772338470 + (0.008485801553 : ℝ) *
        (1 + 2 * (0.282230675087 + 0.011772338470) / (0.560503070407 * 112.645461515322))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12689]

end BstLean.Part269.N12689

/-! The original eight local profiles supply actual 12689 moment certificates. -/
namespace BstLean.Part269.N12689
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12689 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12689 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12689 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052772827346 ∧
    0 ≤ bN 12689 BstLean.Part154.csC (groupTheta g) ∧ bN 12689 BstLean.Part154.csC (groupTheta g) ≤ 0.001381613931 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12689 12689 0.011
      (momentAllowance 12689 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12689 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12689 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12689 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12689 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12689 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229723371354 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12689 0.011
      (momentAllowance 12689 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12689 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12689
/-! The actual computed-centre upper energy formula at 12689. -/
namespace BstLean.Part269.N12689
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12689

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12689
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12689)
open BstLean.Part268 (cell12689)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085522401274
  | 2 => 0.086465742608
  | 3 => 0.087407310184
  | 4 => 0.088348541999
  | 5 => 0.089291176728
  | 6 => 0.090237298298
  | 7 => 0.091189384642
  | 8 => 0.092150360665
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12689 12689 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12689 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003538895953 + 0.003300387184 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S13.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12689

/-! Actual upper energy certificates on all 43 source endpoints at 12689. -/
namespace BstLean.Part269.N12689
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12689)
open BstLean.Part268 (cell12689)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12689 (gMinus 12689) (1 - (cell12689 i).lower) ≤ 1 ∧
    energyUpper 12689 (gMinus 12689) (BstLean.Part211.gPlus 12689)
      (finiteEnergy 12689 12689 0.011) (1 - (cell12689 i).lower) ≤
      (cell12689 i).energy := by
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
      have E := BstLean.Part269.S13.uniformEnergy10 (n := 12689) (by norm_num)
        (q := 1 - (cell12689 ⟨10,by decide⟩).lower)
        (by norm_num [cell12689]) (by norm_num [cell12689])
      exact ⟨E.1,E.2.trans (by norm_num [cell12689])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy11 (n := 12689) (by norm_num)
        (q := 1 - (cell12689 ⟨11,by decide⟩).lower)
        (by norm_num [cell12689]) (by norm_num [cell12689])
      exact ⟨E.1,E.2.trans (by norm_num [cell12689])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy12 (n := 12689) (by norm_num)
        (q := 1 - (cell12689 ⟨12,by decide⟩).lower)
        (by norm_num [cell12689]) (by norm_num [cell12689])
      exact ⟨E.1,E.2.trans (by norm_num [cell12689])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy13 (n := 12689) (by norm_num)
        (q := 1 - (cell12689 ⟨13,by decide⟩).lower)
        (by norm_num [cell12689]) (by norm_num [cell12689])
      exact ⟨E.1,E.2.trans (by norm_num [cell12689])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy14 (n := 12689) (by norm_num)
        (q := 1 - (cell12689 ⟨14,by decide⟩).lower)
        (by norm_num [cell12689]) (by norm_num [cell12689])
      exact ⟨E.1,E.2.trans (by norm_num [cell12689])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy15 (n := 12689) (by norm_num)
        (q := 1 - (cell12689 ⟨15,by decide⟩).lower)
        (by norm_num [cell12689]) (by norm_num [cell12689])
      exact ⟨E.1,E.2.trans (by norm_num [cell12689])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy16 (n := 12689) (by norm_num)
        (q := 1 - (cell12689 ⟨16,by decide⟩).lower)
        (by norm_num [cell12689]) (by norm_num [cell12689])
      exact ⟨E.1,E.2.trans (by norm_num [cell12689])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy17 (n := 12689) (by norm_num)
        (q := 1 - (cell12689 ⟨17,by decide⟩).lower)
        (by norm_num [cell12689]) (by norm_num [cell12689])
      exact ⟨E.1,E.2.trans (by norm_num [cell12689])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy18 (n := 12689) (by norm_num)
        (q := 1 - (cell12689 ⟨18,by decide⟩).lower)
        (by norm_num [cell12689]) (by norm_num [cell12689])
      exact ⟨E.1,E.2.trans (by norm_num [cell12689])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy19 (n := 12689) (by norm_num)
        (q := 1 - (cell12689 ⟨19,by decide⟩).lower)
        (by norm_num [cell12689]) (by norm_num [cell12689])
      exact ⟨E.1,E.2.trans (by norm_num [cell12689])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy20 (n := 12689) (by norm_num)
        (q := 1 - (cell12689 ⟨20,by decide⟩).lower)
        (by norm_num [cell12689]) (by norm_num [cell12689])
      exact ⟨E.1,E.2.trans (by norm_num [cell12689])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy21 (n := 12689) (by norm_num)
        (q := 1 - (cell12689 ⟨21,by decide⟩).lower)
        (by norm_num [cell12689]) (by norm_num [cell12689])
      exact ⟨E.1,E.2.trans (by norm_num [cell12689])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy22 (n := 12689) (by norm_num)
        (q := 1 - (cell12689 ⟨22,by decide⟩).lower)
        (by norm_num [cell12689]) (by norm_num [cell12689])
      exact ⟨E.1,E.2.trans (by norm_num [cell12689])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy23 (n := 12689) (by norm_num)
        (q := 1 - (cell12689 ⟨23,by decide⟩).lower)
        (by norm_num [cell12689]) (by norm_num [cell12689])
      exact ⟨E.1,E.2.trans (by norm_num [cell12689])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy24 (n := 12689) (by norm_num)
        (q := 1 - (cell12689 ⟨24,by decide⟩).lower)
        (by norm_num [cell12689]) (by norm_num [cell12689])
      exact ⟨E.1,E.2.trans (by norm_num [cell12689])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy25 (n := 12689) (by norm_num)
        (q := 1 - (cell12689 ⟨25,by decide⟩).lower)
        (by norm_num [cell12689]) (by norm_num [cell12689])
      exact ⟨E.1,E.2.trans (by norm_num [cell12689])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy26 (n := 12689) (by norm_num)
        (q := 1 - (cell12689 ⟨26,by decide⟩).lower)
        (by norm_num [cell12689]) (by norm_num [cell12689])
      exact ⟨E.1,E.2.trans (by norm_num [cell12689])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy27 (n := 12689) (by norm_num)
        (q := 1 - (cell12689 ⟨27,by decide⟩).lower)
        (by norm_num [cell12689]) (by norm_num [cell12689])
      exact ⟨E.1,E.2.trans (by norm_num [cell12689])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy28 (n := 12689) (by norm_num)
        (q := 1 - (cell12689 ⟨28,by decide⟩).lower)
        (by norm_num [cell12689]) (by norm_num [cell12689])
      exact ⟨E.1,E.2.trans (by norm_num [cell12689])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy29 (n := 12689) (by norm_num)
        (q := 1 - (cell12689 ⟨29,by decide⟩).lower)
        (by norm_num [cell12689]) (by norm_num [cell12689])
      exact ⟨E.1,E.2.trans (by norm_num [cell12689])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy30 (n := 12689) (by norm_num)
        (q := 1 - (cell12689 ⟨30,by decide⟩).lower)
        (by norm_num [cell12689]) (by norm_num [cell12689])
      exact ⟨E.1,E.2.trans (by norm_num [cell12689])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy31 (n := 12689) (by norm_num)
        (q := 1 - (cell12689 ⟨31,by decide⟩).lower)
        (by norm_num [cell12689]) (by norm_num [cell12689])
      exact ⟨E.1,E.2.trans (by norm_num [cell12689])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy32 (n := 12689) (by norm_num)
        (q := 1 - (cell12689 ⟨32,by decide⟩).lower)
        (by norm_num [cell12689]) (by norm_num [cell12689])
      exact ⟨E.1,E.2.trans (by norm_num [cell12689])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy33 (n := 12689) (by norm_num)
        (q := 1 - (cell12689 ⟨33,by decide⟩).lower)
        (by norm_num [cell12689]) (by norm_num [cell12689])
      exact ⟨E.1,E.2.trans (by norm_num [cell12689])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy34 (n := 12689) (by norm_num)
        (q := 1 - (cell12689 ⟨34,by decide⟩).lower)
        (by norm_num [cell12689]) (by norm_num [cell12689])
      exact ⟨E.1,E.2.trans (by norm_num [cell12689])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy35 (n := 12689) (by norm_num)
        (q := 1 - (cell12689 ⟨35,by decide⟩).lower)
        (by norm_num [cell12689]) (by norm_num [cell12689])
      exact ⟨E.1,E.2.trans (by norm_num [cell12689])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy36 (n := 12689) (by norm_num)
        (q := 1 - (cell12689 ⟨36,by decide⟩).lower)
        (by norm_num [cell12689]) (by norm_num [cell12689])
      exact ⟨E.1,E.2.trans (by norm_num [cell12689])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy37 (n := 12689) (by norm_num)
        (q := 1 - (cell12689 ⟨37,by decide⟩).lower)
        (by norm_num [cell12689]) (by norm_num [cell12689])
      exact ⟨E.1,E.2.trans (by norm_num [cell12689])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy38 (n := 12689) (by norm_num)
        (q := 1 - (cell12689 ⟨38,by decide⟩).lower)
        (by norm_num [cell12689]) (by norm_num [cell12689])
      exact ⟨E.1,E.2.trans (by norm_num [cell12689])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy39 (n := 12689) (by norm_num)
        (q := 1 - (cell12689 ⟨39,by decide⟩).lower)
        (by norm_num [cell12689]) (by norm_num [cell12689])
      exact ⟨E.1,E.2.trans (by norm_num [cell12689])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy40 (n := 12689) (by norm_num)
        (q := 1 - (cell12689 ⟨40,by decide⟩).lower)
        (by norm_num [cell12689]) (by norm_num [cell12689])
      exact ⟨E.1,E.2.trans (by norm_num [cell12689])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy41 (n := 12689) (by norm_num)
        (q := 1 - (cell12689 ⟨41,by decide⟩).lower)
        (by norm_num [cell12689]) (by norm_num [cell12689])
      exact ⟨E.1,E.2.trans (by norm_num [cell12689])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy42 (n := 12689) (by norm_num)
        (q := 1 - (cell12689 ⟨42,by decide⟩).lower)
        (by norm_num [cell12689]) (by norm_num [cell12689])
      exact ⟨E.1,E.2.trans (by norm_num [cell12689])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy43 (n := 12689) (by norm_num)
        (q := 1 - (cell12689 ⟨43,by decide⟩).lower)
        (by norm_num [cell12689]) (by norm_num [cell12689])
      exact ⟨E.1,E.2.trans (by norm_num [cell12689])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy44 (n := 12689) (by norm_num)
        (q := 1 - (cell12689 ⟨44,by decide⟩).lower)
        (by norm_num [cell12689]) (by norm_num [cell12689])
      exact ⟨E.1,E.2.trans (by norm_num [cell12689])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy45 (n := 12689) (by norm_num)
        (q := 1 - (cell12689 ⟨45,by decide⟩).lower)
        (by norm_num [cell12689]) (by norm_num [cell12689])
      exact ⟨E.1,E.2.trans (by norm_num [cell12689])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy46 (n := 12689) (by norm_num)
        (q := 1 - (cell12689 ⟨46,by decide⟩).lower)
        (by norm_num [cell12689]) (by norm_num [cell12689])
      exact ⟨E.1,E.2.trans (by norm_num [cell12689])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy47 (n := 12689) (by norm_num)
        (q := 1 - (cell12689 ⟨47,by decide⟩).lower)
        (by norm_num [cell12689]) (by norm_num [cell12689])
      exact ⟨E.1,E.2.trans (by norm_num [cell12689])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy48 (n := 12689) (by norm_num)
        (q := 1 - (cell12689 ⟨48,by decide⟩).lower)
        (by norm_num [cell12689]) (by norm_num [cell12689])
      exact ⟨E.1,E.2.trans (by norm_num [cell12689])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy49 (n := 12689) (by norm_num)
        (q := 1 - (cell12689 ⟨49,by decide⟩).lower)
        (by norm_num [cell12689]) (by norm_num [cell12689])
      exact ⟨E.1,E.2.trans (by norm_num [cell12689])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy50 (n := 12689) (by norm_num)
        (q := 1 - (cell12689 ⟨50,by decide⟩).lower)
        (by norm_num [cell12689]) (by norm_num [cell12689])
      exact ⟨E.1,E.2.trans (by norm_num [cell12689])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy51 (n := 12689) (by norm_num)
        (q := 1 - (cell12689 ⟨51,by decide⟩).lower)
        (by norm_num [cell12689]) (by norm_num [cell12689])
      exact ⟨E.1,E.2.trans (by norm_num [cell12689])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy52 (n := 12689) (by norm_num)
        (q := 1 - (cell12689 ⟨52,by decide⟩).lower)
        (by norm_num [cell12689]) (by norm_num [cell12689])
      exact ⟨E.1,E.2.trans (by norm_num [cell12689])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12689

/-! Source-cell containment and simple scalar guards at 12689. -/
namespace BstLean.Part269.N12689
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12689)
open BstLean.Part268 (cell12689)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12689 ⟨10,by decide⟩).lower ∧ (cell12689 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12689 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12689 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12689 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12689 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12689 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12689,cell12689,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12689 ⟨11,by decide⟩).lower ∧ (cell12689 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12689 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12689 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12689 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12689 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12689 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12689,cell12689,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12689 ⟨12,by decide⟩).lower ∧ (cell12689 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12689 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12689 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12689 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12689 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12689 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12689,cell12689,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12689 ⟨13,by decide⟩).lower ∧ (cell12689 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12689 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12689 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12689 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12689 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12689 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12689,cell12689,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12689 ⟨14,by decide⟩).lower ∧ (cell12689 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12689 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12689 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12689 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12689 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12689 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12689,cell12689,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12689 ⟨15,by decide⟩).lower ∧ (cell12689 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12689 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12689 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12689 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12689 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12689 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12689,cell12689,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12689 ⟨16,by decide⟩).lower ∧ (cell12689 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12689 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12689 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12689 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12689 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12689 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12689,cell12689,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12689 ⟨17,by decide⟩).lower ∧ (cell12689 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12689 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12689 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12689 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12689 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12689 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12689,cell12689,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12689 ⟨18,by decide⟩).lower ∧ (cell12689 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12689 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12689 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12689 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12689 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12689 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12689,cell12689,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12689 ⟨19,by decide⟩).lower ∧ (cell12689 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12689 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12689 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12689 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12689 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12689 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12689,cell12689,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12689 ⟨20,by decide⟩).lower ∧ (cell12689 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12689 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12689 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12689 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12689 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12689 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12689,cell12689,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12689 ⟨21,by decide⟩).lower ∧ (cell12689 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12689 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12689 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12689 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12689 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12689 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12689,cell12689,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12689 ⟨22,by decide⟩).lower ∧ (cell12689 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12689 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12689 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12689 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12689 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12689 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12689,cell12689,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12689 ⟨23,by decide⟩).lower ∧ (cell12689 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12689 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12689 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12689 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12689 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12689 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12689,cell12689,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12689 ⟨24,by decide⟩).lower ∧ (cell12689 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12689 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12689 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12689 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12689 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12689 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12689,cell12689,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12689 ⟨25,by decide⟩).lower ∧ (cell12689 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12689 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12689 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12689 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12689 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12689 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12689,cell12689,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12689 ⟨26,by decide⟩).lower ∧ (cell12689 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12689 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12689 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12689 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12689 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12689 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12689,cell12689,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12689 ⟨27,by decide⟩).lower ∧ (cell12689 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12689 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12689 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12689 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12689 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12689 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12689,cell12689,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12689 ⟨28,by decide⟩).lower ∧ (cell12689 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12689 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12689 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12689 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12689 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12689 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12689,cell12689,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12689 ⟨29,by decide⟩).lower ∧ (cell12689 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12689 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12689 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12689 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12689 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12689 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12689,cell12689,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12689 ⟨30,by decide⟩).lower ∧ (cell12689 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12689 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12689 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12689 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12689 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12689 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12689,cell12689,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12689 ⟨31,by decide⟩).lower ∧ (cell12689 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12689 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12689 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12689 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12689 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12689 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12689,cell12689,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12689 ⟨32,by decide⟩).lower ∧ (cell12689 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12689 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12689 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12689 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12689 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12689 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12689,cell12689,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12689 ⟨33,by decide⟩).lower ∧ (cell12689 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12689 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12689 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12689 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12689 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12689 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12689,cell12689,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12689 ⟨34,by decide⟩).lower ∧ (cell12689 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12689 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12689 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12689 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12689 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12689 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12689,cell12689,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12689 ⟨35,by decide⟩).lower ∧ (cell12689 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12689 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12689 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12689 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12689 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12689 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12689,cell12689,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12689 ⟨36,by decide⟩).lower ∧ (cell12689 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12689 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12689 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12689 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12689 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12689 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12689,cell12689,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12689 ⟨37,by decide⟩).lower ∧ (cell12689 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12689 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12689 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12689 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12689 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12689 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12689,cell12689,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12689 ⟨38,by decide⟩).lower ∧ (cell12689 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12689 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12689 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12689 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12689 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12689 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12689,cell12689,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12689 ⟨39,by decide⟩).lower ∧ (cell12689 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12689 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12689 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12689 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12689 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12689 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12689,cell12689,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12689 ⟨40,by decide⟩).lower ∧ (cell12689 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12689 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12689 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12689 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12689 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12689 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12689,cell12689,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12689 ⟨41,by decide⟩).lower ∧ (cell12689 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12689 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12689 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12689 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12689 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12689 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12689,cell12689,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12689 ⟨42,by decide⟩).lower ∧ (cell12689 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12689 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12689 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12689 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12689 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12689 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12689,cell12689,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12689 ⟨43,by decide⟩).lower ∧ (cell12689 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12689 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12689 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12689 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12689 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12689 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12689,cell12689,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12689 ⟨44,by decide⟩).lower ∧ (cell12689 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12689 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12689 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12689 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12689 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12689 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12689,cell12689,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12689 ⟨45,by decide⟩).lower ∧ (cell12689 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12689 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12689 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12689 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12689 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12689 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12689,cell12689,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12689 ⟨46,by decide⟩).lower ∧ (cell12689 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12689 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12689 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12689 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12689 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12689 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12689,cell12689,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12689 ⟨47,by decide⟩).lower ∧ (cell12689 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12689 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12689 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12689 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12689 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12689 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12689,cell12689,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12689 ⟨48,by decide⟩).lower ∧ (cell12689 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12689 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12689 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12689 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12689 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12689 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12689,cell12689,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12689 ⟨49,by decide⟩).lower ∧ (cell12689 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12689 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12689 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12689 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12689 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12689 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12689,cell12689,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12689 ⟨50,by decide⟩).lower ∧ (cell12689 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12689 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12689 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12689 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12689 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12689 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12689,cell12689,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12689 ⟨51,by decide⟩).lower ∧ (cell12689 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12689 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12689 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12689 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12689 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12689 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12689,cell12689,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12689 ⟨52,by decide⟩).lower ∧ (cell12689 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12689 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12689 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12689 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12689 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12689 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12689,cell12689,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12689 i).lower ∧
    (cell12689 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12689 i).upper ≤ (0.532 : ℝ) ∧
    (cell12689 i).centre ≤ (0.1 : ℝ) ∧ (cell12689 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12689 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12689 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12689

/-! The local source numeric instances at 12689 have no network premises. -/
namespace BstLean.Part269.N12689
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12689)
open BstLean.Part268 (cell12689)

noncomputable def sourceNumerics12689 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12689 (cell12689 i)
      scalarRow12689.M scalarRow12689.H scalarRow12689.xi := by
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
    energy_allowance := scalarRow12689.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12689]
    centre_nonneg := (scalarRow12689.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D13.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12689])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12689
/-! Actual 12690 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12690
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12690 ≤ (1.035823451579 : ℝ) := by
  have hr : (112.649900133111 : ℝ) ≤ √(12690 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.649900133111 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12690 12690 (11 / 1000) ≤
    (0.008485467194 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12690) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.649900133111 : ℝ) ≤ √(12690 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12690)
  have hdiv : K / √(12690 : ℝ) ≤ K / 112.649900133111 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.649900133111 ≤ (0.008485467194 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12690.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12690 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12690 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12690 := gPlus_lower 12690
end BstLean.Part269.N12690

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12690
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035823451578 : ℝ) ≤ wn 12690 := by
  have hn : √(12690 : ℝ) ≤ 112.649900133112 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12690 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.649900133112 ≤ 2 / √(12690 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000252082820 : ℝ) ≤ rhoBar 12690 BstLean.Part154.csC ∧
    rhoBar 12690 BstLean.Part154.csC ≤ 0.000252083210 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035823451578 : ℝ) / (1.295212 * 12690) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035823451579 : ℝ) / (1.29521 * 12690) := by gcongr
      _ ≤ (0.000252083210 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12690 BstLean.Part154.csC) ≤ 0.001008396386 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12690 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12690 BstLean.Part154.csC) (piBar (rhoBar 12690 BstLean.Part154.csC)) ≤ 0.000192542864 ∧
    cc1 (rhoBar 12690 BstLean.Part154.csC) (piBar (rhoBar 12690 BstLean.Part154.csC)) ≤ 0.000122516301 ∧
    cc2 (rhoBar 12690 BstLean.Part154.csC) ≤ 0.000071121650 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12690 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12690 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12690 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12690 BstLean.Part154.csC * nuR (rhoBar 12690 BstLean.Part154.csC)) ≤ 0.000504182307 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000252083210 : ℝ) * 0.001008396386 := by gcongr
      _ ≤ (0.000504182307 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12690 BstLean.Part154.csC) * nuR (rhoBar 12690 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001008396386 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12690 BstLean.Part154.csC) * rhoBar 12690 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000252083210 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000252083210 / 2 + 0.399 * 0.001008396386 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000192542864 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000504182307 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122516301 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000252083210 / 1.414213562 := by gcongr
      _ ≤ (0.000071121650 : ℝ) := by norm_num

end BstLean.Part269.N12690

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12690
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12690 BstLean.Part154.csC) (piBar (rhoBar 12690 BstLean.Part154.csC)) ≤ 1.60100E-7 := by
  have hr0 : 0 ≤ rhoBar 12690 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12690 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12690 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12690 BstLean.Part154.csC) (piBar (rhoBar 12690 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12690 BstLean.Part154.csC) (piBar (rhoBar 12690 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12690 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000192542864 : ℝ) ^ 2 + 0.000122516301 ^ 2 + 3 * 0.000071121650 ^ 2 +
        2 * 0.797885 * 0.000192542864 * 0.000122516301 + 2 * 0.000192542864 * 0.000071121650 +
        4 * 0.797885 * 0.000122516301 * 0.000071121650 := by gcongr
    _ ≤ (1.60100E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12690 BstLean.Part154.csC Θ ≤ 0.002631442073 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12690 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12690 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12690 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12690 BstLean.Part154.csC) (piBar (rhoBar 12690 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12690 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035823451579 * 1.60100E-7 / (0.000252082820 : ℝ) := by gcongr
    _ ≤ 0.002631442073 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12690 BstLean.Part154.csC Θ ≤ 0.002919757418 + 0.000664920718 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12690 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12690 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12690 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035823451579 : ℝ) * ((2 * Θ * 0.000252083210 +
        (6863 / 10000) * 0.000252083210 * 12690 * 0.001008396386) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002919757418 + 0.000664920718 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12690 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12690 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12690 0.011 Θ ∧ gammaRatio 12690 0.011 Θ ≤ 0.000086659689 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12690 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035823451579 : ℝ) * 0.525 / ((1 - 0.011) * 12690) := by gcongr
      _ ≤ (0.000086659689 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12690 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12690 0.011 Θ) :=
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
    badAllowance 12690 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000615501984 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12690 BstLean.Part154.csC) 1.22 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 2 (rhoBar 12690 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12690 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12690 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12690 0.011 Θ) 1.12 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 1 (gammaRatio 12690 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12690 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12690 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12690 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12690 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035823451579 : ℝ) * 12690 *
        (2.2721E-8 / 1.1045361 + 2.7751E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000615501984 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12690 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003535259402 + 0.003296362791 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12690

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12690
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12690 BstLean.Part154.csC) (piBar (rhoBar 12690 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12690 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12690 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12690 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12690 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12690 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12690 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12690 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12690 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12690 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12690 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12690 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12690 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12690 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12690 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052505212405 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12690) ≤ 0.010601319484 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12690 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035823451579)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010601319484 + 2 * 0.737676 / 12690) := by gcongr
    _ ≤ (0.052505212405 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12690 12 ≤ 0.0015 := by
  exact BstLean.Part269.S13.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12690

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12690
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560503115705 : ℝ) ≤ plow 12690 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12690) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052772449868)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001381507089) : eMP 12690 0.011 xi bn ≤ 0.001189332392 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12690 : ℝ) * (1 - 0.011))) ≤ 0.000588061250 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001381507089 / (12690 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000588061250 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000588061250 : ℝ) + 3.141593 * 0.052772449868 / (12690 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001189332392 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052772449868)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001381507089) : PiBarMP 12690 12 0.011 xi bn ≤ 0.161315230827 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12690 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037168630443 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.028612416650 : ℝ) ≤ √((12690 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.649900133111 : ℝ) ≤ √(12690 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12690) ≤ 0.123678833682 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037168630443 + 0.052772449868 * 1.772454 / (2 * (112.028612416650 : ℝ))) * (1 + 0.001189332392) +
        8 / (12690 * 112.649900133111) + 0.123678833682 := by gcongr
    _ ≤ (0.161315230827 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052772449868)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001381507089) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282227762165) :
    parallelOracle 12690 0.011 xi bn cd ≤ 0.162306511451 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12690 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12690 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560503115705 : ℝ) ≤ plow 12690 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.649900133111 : ℝ) ≤ √(12690 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282227762165 : ℝ) / (2 * 0.560503115705 * 112.649900133111)) * 0.161315230827 +
        0.282227762165 ^ 2 / (2 * 0.560503115705 * 112.649900133111) := by gcongr
    _ ≤ (0.162306511451 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052772449868) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001381507089)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282227762165) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12690 12690 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560503115705 : ℝ) ≤ plow 12690 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.649900133111 : ℝ) ≤ √(12690 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12690 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12690 Θ 1.22 ≤ 0.011771874618 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.649900133111 := by gcongr <;> linarith
      _ ≤ (0.011771874618 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12690 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12690 12690 0.011 ≤ 0.008485467194 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12690 12690 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12690 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12690 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12690 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12690 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162306511451 + 0.011771874618 + (0.008485467194 : ℝ) *
        (1 + 2 * (0.282227762165 + 0.011771874618) / (0.560503115705 * 112.649900133111))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12690]

end BstLean.Part269.N12690

/-! The original eight local profiles supply actual 12690 moment certificates. -/
namespace BstLean.Part269.N12690
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12690 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12690 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12690 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052772449868 ∧
    0 ≤ bN 12690 BstLean.Part154.csC (groupTheta g) ∧ bN 12690 BstLean.Part154.csC (groupTheta g) ≤ 0.001381507089 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12690 12690 0.011
      (momentAllowance 12690 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12690 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12690 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12690 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12690 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12690 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229722549760 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12690 0.011
      (momentAllowance 12690 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12690 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12690
/-! The actual computed-centre upper energy formula at 12690. -/
namespace BstLean.Part269.N12690
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12690

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12690
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12690)
open BstLean.Part268 (cell12690)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085519473538
  | 2 => 0.086462760822
  | 3 => 0.087404266422
  | 4 => 0.088345426512
  | 5 => 0.089287977622
  | 6 => 0.090234001173
  | 7 => 0.091185972189
  | 8 => 0.092146812220
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12690 12690 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12690 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003538895953 + 0.003300387184 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S13.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12690

/-! Actual upper energy certificates on all 43 source endpoints at 12690. -/
namespace BstLean.Part269.N12690
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12690)
open BstLean.Part268 (cell12690)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12690 (gMinus 12690) (1 - (cell12690 i).lower) ≤ 1 ∧
    energyUpper 12690 (gMinus 12690) (BstLean.Part211.gPlus 12690)
      (finiteEnergy 12690 12690 0.011) (1 - (cell12690 i).lower) ≤
      (cell12690 i).energy := by
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
      have E := BstLean.Part269.S13.uniformEnergy10 (n := 12690) (by norm_num)
        (q := 1 - (cell12690 ⟨10,by decide⟩).lower)
        (by norm_num [cell12690]) (by norm_num [cell12690])
      exact ⟨E.1,E.2.trans (by norm_num [cell12690])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy11 (n := 12690) (by norm_num)
        (q := 1 - (cell12690 ⟨11,by decide⟩).lower)
        (by norm_num [cell12690]) (by norm_num [cell12690])
      exact ⟨E.1,E.2.trans (by norm_num [cell12690])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy12 (n := 12690) (by norm_num)
        (q := 1 - (cell12690 ⟨12,by decide⟩).lower)
        (by norm_num [cell12690]) (by norm_num [cell12690])
      exact ⟨E.1,E.2.trans (by norm_num [cell12690])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy13 (n := 12690) (by norm_num)
        (q := 1 - (cell12690 ⟨13,by decide⟩).lower)
        (by norm_num [cell12690]) (by norm_num [cell12690])
      exact ⟨E.1,E.2.trans (by norm_num [cell12690])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy14 (n := 12690) (by norm_num)
        (q := 1 - (cell12690 ⟨14,by decide⟩).lower)
        (by norm_num [cell12690]) (by norm_num [cell12690])
      exact ⟨E.1,E.2.trans (by norm_num [cell12690])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy15 (n := 12690) (by norm_num)
        (q := 1 - (cell12690 ⟨15,by decide⟩).lower)
        (by norm_num [cell12690]) (by norm_num [cell12690])
      exact ⟨E.1,E.2.trans (by norm_num [cell12690])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy16 (n := 12690) (by norm_num)
        (q := 1 - (cell12690 ⟨16,by decide⟩).lower)
        (by norm_num [cell12690]) (by norm_num [cell12690])
      exact ⟨E.1,E.2.trans (by norm_num [cell12690])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy17 (n := 12690) (by norm_num)
        (q := 1 - (cell12690 ⟨17,by decide⟩).lower)
        (by norm_num [cell12690]) (by norm_num [cell12690])
      exact ⟨E.1,E.2.trans (by norm_num [cell12690])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy18 (n := 12690) (by norm_num)
        (q := 1 - (cell12690 ⟨18,by decide⟩).lower)
        (by norm_num [cell12690]) (by norm_num [cell12690])
      exact ⟨E.1,E.2.trans (by norm_num [cell12690])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy19 (n := 12690) (by norm_num)
        (q := 1 - (cell12690 ⟨19,by decide⟩).lower)
        (by norm_num [cell12690]) (by norm_num [cell12690])
      exact ⟨E.1,E.2.trans (by norm_num [cell12690])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy20 (n := 12690) (by norm_num)
        (q := 1 - (cell12690 ⟨20,by decide⟩).lower)
        (by norm_num [cell12690]) (by norm_num [cell12690])
      exact ⟨E.1,E.2.trans (by norm_num [cell12690])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy21 (n := 12690) (by norm_num)
        (q := 1 - (cell12690 ⟨21,by decide⟩).lower)
        (by norm_num [cell12690]) (by norm_num [cell12690])
      exact ⟨E.1,E.2.trans (by norm_num [cell12690])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy22 (n := 12690) (by norm_num)
        (q := 1 - (cell12690 ⟨22,by decide⟩).lower)
        (by norm_num [cell12690]) (by norm_num [cell12690])
      exact ⟨E.1,E.2.trans (by norm_num [cell12690])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy23 (n := 12690) (by norm_num)
        (q := 1 - (cell12690 ⟨23,by decide⟩).lower)
        (by norm_num [cell12690]) (by norm_num [cell12690])
      exact ⟨E.1,E.2.trans (by norm_num [cell12690])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy24 (n := 12690) (by norm_num)
        (q := 1 - (cell12690 ⟨24,by decide⟩).lower)
        (by norm_num [cell12690]) (by norm_num [cell12690])
      exact ⟨E.1,E.2.trans (by norm_num [cell12690])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy25 (n := 12690) (by norm_num)
        (q := 1 - (cell12690 ⟨25,by decide⟩).lower)
        (by norm_num [cell12690]) (by norm_num [cell12690])
      exact ⟨E.1,E.2.trans (by norm_num [cell12690])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy26 (n := 12690) (by norm_num)
        (q := 1 - (cell12690 ⟨26,by decide⟩).lower)
        (by norm_num [cell12690]) (by norm_num [cell12690])
      exact ⟨E.1,E.2.trans (by norm_num [cell12690])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy27 (n := 12690) (by norm_num)
        (q := 1 - (cell12690 ⟨27,by decide⟩).lower)
        (by norm_num [cell12690]) (by norm_num [cell12690])
      exact ⟨E.1,E.2.trans (by norm_num [cell12690])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy28 (n := 12690) (by norm_num)
        (q := 1 - (cell12690 ⟨28,by decide⟩).lower)
        (by norm_num [cell12690]) (by norm_num [cell12690])
      exact ⟨E.1,E.2.trans (by norm_num [cell12690])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy29 (n := 12690) (by norm_num)
        (q := 1 - (cell12690 ⟨29,by decide⟩).lower)
        (by norm_num [cell12690]) (by norm_num [cell12690])
      exact ⟨E.1,E.2.trans (by norm_num [cell12690])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy30 (n := 12690) (by norm_num)
        (q := 1 - (cell12690 ⟨30,by decide⟩).lower)
        (by norm_num [cell12690]) (by norm_num [cell12690])
      exact ⟨E.1,E.2.trans (by norm_num [cell12690])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy31 (n := 12690) (by norm_num)
        (q := 1 - (cell12690 ⟨31,by decide⟩).lower)
        (by norm_num [cell12690]) (by norm_num [cell12690])
      exact ⟨E.1,E.2.trans (by norm_num [cell12690])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy32 (n := 12690) (by norm_num)
        (q := 1 - (cell12690 ⟨32,by decide⟩).lower)
        (by norm_num [cell12690]) (by norm_num [cell12690])
      exact ⟨E.1,E.2.trans (by norm_num [cell12690])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy33 (n := 12690) (by norm_num)
        (q := 1 - (cell12690 ⟨33,by decide⟩).lower)
        (by norm_num [cell12690]) (by norm_num [cell12690])
      exact ⟨E.1,E.2.trans (by norm_num [cell12690])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy34 (n := 12690) (by norm_num)
        (q := 1 - (cell12690 ⟨34,by decide⟩).lower)
        (by norm_num [cell12690]) (by norm_num [cell12690])
      exact ⟨E.1,E.2.trans (by norm_num [cell12690])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy35 (n := 12690) (by norm_num)
        (q := 1 - (cell12690 ⟨35,by decide⟩).lower)
        (by norm_num [cell12690]) (by norm_num [cell12690])
      exact ⟨E.1,E.2.trans (by norm_num [cell12690])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy36 (n := 12690) (by norm_num)
        (q := 1 - (cell12690 ⟨36,by decide⟩).lower)
        (by norm_num [cell12690]) (by norm_num [cell12690])
      exact ⟨E.1,E.2.trans (by norm_num [cell12690])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy37 (n := 12690) (by norm_num)
        (q := 1 - (cell12690 ⟨37,by decide⟩).lower)
        (by norm_num [cell12690]) (by norm_num [cell12690])
      exact ⟨E.1,E.2.trans (by norm_num [cell12690])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy38 (n := 12690) (by norm_num)
        (q := 1 - (cell12690 ⟨38,by decide⟩).lower)
        (by norm_num [cell12690]) (by norm_num [cell12690])
      exact ⟨E.1,E.2.trans (by norm_num [cell12690])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy39 (n := 12690) (by norm_num)
        (q := 1 - (cell12690 ⟨39,by decide⟩).lower)
        (by norm_num [cell12690]) (by norm_num [cell12690])
      exact ⟨E.1,E.2.trans (by norm_num [cell12690])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy40 (n := 12690) (by norm_num)
        (q := 1 - (cell12690 ⟨40,by decide⟩).lower)
        (by norm_num [cell12690]) (by norm_num [cell12690])
      exact ⟨E.1,E.2.trans (by norm_num [cell12690])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy41 (n := 12690) (by norm_num)
        (q := 1 - (cell12690 ⟨41,by decide⟩).lower)
        (by norm_num [cell12690]) (by norm_num [cell12690])
      exact ⟨E.1,E.2.trans (by norm_num [cell12690])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy42 (n := 12690) (by norm_num)
        (q := 1 - (cell12690 ⟨42,by decide⟩).lower)
        (by norm_num [cell12690]) (by norm_num [cell12690])
      exact ⟨E.1,E.2.trans (by norm_num [cell12690])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy43 (n := 12690) (by norm_num)
        (q := 1 - (cell12690 ⟨43,by decide⟩).lower)
        (by norm_num [cell12690]) (by norm_num [cell12690])
      exact ⟨E.1,E.2.trans (by norm_num [cell12690])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy44 (n := 12690) (by norm_num)
        (q := 1 - (cell12690 ⟨44,by decide⟩).lower)
        (by norm_num [cell12690]) (by norm_num [cell12690])
      exact ⟨E.1,E.2.trans (by norm_num [cell12690])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy45 (n := 12690) (by norm_num)
        (q := 1 - (cell12690 ⟨45,by decide⟩).lower)
        (by norm_num [cell12690]) (by norm_num [cell12690])
      exact ⟨E.1,E.2.trans (by norm_num [cell12690])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy46 (n := 12690) (by norm_num)
        (q := 1 - (cell12690 ⟨46,by decide⟩).lower)
        (by norm_num [cell12690]) (by norm_num [cell12690])
      exact ⟨E.1,E.2.trans (by norm_num [cell12690])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy47 (n := 12690) (by norm_num)
        (q := 1 - (cell12690 ⟨47,by decide⟩).lower)
        (by norm_num [cell12690]) (by norm_num [cell12690])
      exact ⟨E.1,E.2.trans (by norm_num [cell12690])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy48 (n := 12690) (by norm_num)
        (q := 1 - (cell12690 ⟨48,by decide⟩).lower)
        (by norm_num [cell12690]) (by norm_num [cell12690])
      exact ⟨E.1,E.2.trans (by norm_num [cell12690])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy49 (n := 12690) (by norm_num)
        (q := 1 - (cell12690 ⟨49,by decide⟩).lower)
        (by norm_num [cell12690]) (by norm_num [cell12690])
      exact ⟨E.1,E.2.trans (by norm_num [cell12690])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy50 (n := 12690) (by norm_num)
        (q := 1 - (cell12690 ⟨50,by decide⟩).lower)
        (by norm_num [cell12690]) (by norm_num [cell12690])
      exact ⟨E.1,E.2.trans (by norm_num [cell12690])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy51 (n := 12690) (by norm_num)
        (q := 1 - (cell12690 ⟨51,by decide⟩).lower)
        (by norm_num [cell12690]) (by norm_num [cell12690])
      exact ⟨E.1,E.2.trans (by norm_num [cell12690])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy52 (n := 12690) (by norm_num)
        (q := 1 - (cell12690 ⟨52,by decide⟩).lower)
        (by norm_num [cell12690]) (by norm_num [cell12690])
      exact ⟨E.1,E.2.trans (by norm_num [cell12690])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12690

/-! Source-cell containment and simple scalar guards at 12690. -/
namespace BstLean.Part269.N12690
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12690)
open BstLean.Part268 (cell12690)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12690 ⟨10,by decide⟩).lower ∧ (cell12690 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12690 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12690 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12690 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12690 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12690 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12690,cell12690,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12690 ⟨11,by decide⟩).lower ∧ (cell12690 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12690 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12690 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12690 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12690 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12690 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12690,cell12690,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12690 ⟨12,by decide⟩).lower ∧ (cell12690 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12690 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12690 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12690 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12690 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12690 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12690,cell12690,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12690 ⟨13,by decide⟩).lower ∧ (cell12690 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12690 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12690 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12690 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12690 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12690 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12690,cell12690,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12690 ⟨14,by decide⟩).lower ∧ (cell12690 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12690 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12690 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12690 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12690 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12690 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12690,cell12690,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12690 ⟨15,by decide⟩).lower ∧ (cell12690 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12690 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12690 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12690 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12690 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12690 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12690,cell12690,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12690 ⟨16,by decide⟩).lower ∧ (cell12690 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12690 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12690 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12690 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12690 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12690 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12690,cell12690,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12690 ⟨17,by decide⟩).lower ∧ (cell12690 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12690 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12690 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12690 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12690 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12690 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12690,cell12690,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12690 ⟨18,by decide⟩).lower ∧ (cell12690 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12690 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12690 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12690 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12690 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12690 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12690,cell12690,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12690 ⟨19,by decide⟩).lower ∧ (cell12690 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12690 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12690 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12690 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12690 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12690 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12690,cell12690,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12690 ⟨20,by decide⟩).lower ∧ (cell12690 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12690 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12690 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12690 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12690 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12690 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12690,cell12690,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12690 ⟨21,by decide⟩).lower ∧ (cell12690 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12690 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12690 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12690 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12690 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12690 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12690,cell12690,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12690 ⟨22,by decide⟩).lower ∧ (cell12690 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12690 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12690 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12690 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12690 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12690 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12690,cell12690,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12690 ⟨23,by decide⟩).lower ∧ (cell12690 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12690 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12690 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12690 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12690 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12690 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12690,cell12690,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12690 ⟨24,by decide⟩).lower ∧ (cell12690 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12690 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12690 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12690 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12690 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12690 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12690,cell12690,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12690 ⟨25,by decide⟩).lower ∧ (cell12690 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12690 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12690 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12690 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12690 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12690 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12690,cell12690,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12690 ⟨26,by decide⟩).lower ∧ (cell12690 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12690 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12690 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12690 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12690 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12690 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12690,cell12690,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12690 ⟨27,by decide⟩).lower ∧ (cell12690 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12690 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12690 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12690 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12690 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12690 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12690,cell12690,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12690 ⟨28,by decide⟩).lower ∧ (cell12690 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12690 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12690 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12690 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12690 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12690 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12690,cell12690,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12690 ⟨29,by decide⟩).lower ∧ (cell12690 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12690 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12690 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12690 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12690 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12690 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12690,cell12690,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12690 ⟨30,by decide⟩).lower ∧ (cell12690 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12690 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12690 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12690 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12690 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12690 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12690,cell12690,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12690 ⟨31,by decide⟩).lower ∧ (cell12690 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12690 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12690 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12690 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12690 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12690 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12690,cell12690,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12690 ⟨32,by decide⟩).lower ∧ (cell12690 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12690 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12690 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12690 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12690 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12690 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12690,cell12690,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12690 ⟨33,by decide⟩).lower ∧ (cell12690 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12690 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12690 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12690 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12690 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12690 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12690,cell12690,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12690 ⟨34,by decide⟩).lower ∧ (cell12690 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12690 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12690 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12690 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12690 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12690 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12690,cell12690,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12690 ⟨35,by decide⟩).lower ∧ (cell12690 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12690 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12690 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12690 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12690 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12690 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12690,cell12690,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12690 ⟨36,by decide⟩).lower ∧ (cell12690 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12690 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12690 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12690 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12690 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12690 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12690,cell12690,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12690 ⟨37,by decide⟩).lower ∧ (cell12690 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12690 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12690 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12690 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12690 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12690 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12690,cell12690,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12690 ⟨38,by decide⟩).lower ∧ (cell12690 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12690 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12690 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12690 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12690 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12690 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12690,cell12690,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12690 ⟨39,by decide⟩).lower ∧ (cell12690 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12690 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12690 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12690 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12690 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12690 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12690,cell12690,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12690 ⟨40,by decide⟩).lower ∧ (cell12690 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12690 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12690 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12690 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12690 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12690 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12690,cell12690,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12690 ⟨41,by decide⟩).lower ∧ (cell12690 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12690 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12690 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12690 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12690 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12690 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12690,cell12690,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12690 ⟨42,by decide⟩).lower ∧ (cell12690 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12690 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12690 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12690 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12690 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12690 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12690,cell12690,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12690 ⟨43,by decide⟩).lower ∧ (cell12690 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12690 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12690 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12690 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12690 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12690 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12690,cell12690,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12690 ⟨44,by decide⟩).lower ∧ (cell12690 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12690 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12690 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12690 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12690 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12690 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12690,cell12690,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12690 ⟨45,by decide⟩).lower ∧ (cell12690 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12690 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12690 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12690 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12690 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12690 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12690,cell12690,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12690 ⟨46,by decide⟩).lower ∧ (cell12690 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12690 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12690 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12690 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12690 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12690 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12690,cell12690,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12690 ⟨47,by decide⟩).lower ∧ (cell12690 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12690 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12690 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12690 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12690 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12690 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12690,cell12690,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12690 ⟨48,by decide⟩).lower ∧ (cell12690 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12690 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12690 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12690 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12690 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12690 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12690,cell12690,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12690 ⟨49,by decide⟩).lower ∧ (cell12690 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12690 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12690 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12690 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12690 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12690 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12690,cell12690,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12690 ⟨50,by decide⟩).lower ∧ (cell12690 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12690 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12690 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12690 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12690 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12690 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12690,cell12690,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12690 ⟨51,by decide⟩).lower ∧ (cell12690 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12690 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12690 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12690 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12690 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12690 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12690,cell12690,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12690 ⟨52,by decide⟩).lower ∧ (cell12690 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12690 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12690 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12690 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12690 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12690 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12690,cell12690,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12690 i).lower ∧
    (cell12690 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12690 i).upper ≤ (0.532 : ℝ) ∧
    (cell12690 i).centre ≤ (0.1 : ℝ) ∧ (cell12690 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12690 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12690 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12690

/-! The local source numeric instances at 12690 have no network premises. -/
namespace BstLean.Part269.N12690
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12690)
open BstLean.Part268 (cell12690)

noncomputable def sourceNumerics12690 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12690 (cell12690 i)
      scalarRow12690.M scalarRow12690.H scalarRow12690.xi := by
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
    energy_allowance := scalarRow12690.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12690]
    centre_nonneg := (scalarRow12690.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D13.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12690])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12690
/-! Actual 12691 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12691
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12691 ≤ (1.035822027761 : ℝ) := by
  have hr : (112.654338576017 : ℝ) ≤ √(12691 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.654338576017 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12691 12691 (11 / 1000) ≤
    (0.008485132875 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12691) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.654338576017 : ℝ) ≤ √(12691 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12691)
  have hdiv : K / √(12691 : ℝ) ≤ K / 112.654338576017 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.654338576017 ≤ (0.008485132875 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12691.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12691 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12691 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12691 := gPlus_lower 12691
end BstLean.Part269.N12691

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12691
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035822027760 : ℝ) ≤ wn 12691 := by
  have hn : √(12691 : ℝ) ≤ 112.654338576018 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12691 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.654338576018 ≤ 2 / √(12691 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000252062610 : ℝ) ≤ rhoBar 12691 BstLean.Part154.csC ∧
    rhoBar 12691 BstLean.Part154.csC ≤ 0.000252063001 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035822027760 : ℝ) / (1.295212 * 12691) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035822027761 : ℝ) / (1.29521 * 12691) := by gcongr
      _ ≤ (0.000252063001 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12691 BstLean.Part154.csC) ≤ 0.001008315540 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12691 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12691 BstLean.Part154.csC) (piBar (rhoBar 12691 BstLean.Part154.csC)) ≤ 0.000192527427 ∧
    cc1 (rhoBar 12691 BstLean.Part154.csC) (piBar (rhoBar 12691 BstLean.Part154.csC)) ≤ 0.000122506479 ∧
    cc2 (rhoBar 12691 BstLean.Part154.csC) ≤ 0.000071115948 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12691 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12691 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12691 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12691 BstLean.Part154.csC * nuR (rhoBar 12691 BstLean.Part154.csC)) ≤ 0.000504141886 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000252063001 : ℝ) * 0.001008315540 := by gcongr
      _ ≤ (0.000504141886 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12691 BstLean.Part154.csC) * nuR (rhoBar 12691 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001008315540 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12691 BstLean.Part154.csC) * rhoBar 12691 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000252063001 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000252063001 / 2 + 0.399 * 0.001008315540 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000192527427 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000504141886 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122506479 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000252063001 / 1.414213562 := by gcongr
      _ ≤ (0.000071115948 : ℝ) := by norm_num

end BstLean.Part269.N12691

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12691
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12691 BstLean.Part154.csC) (piBar (rhoBar 12691 BstLean.Part154.csC)) ≤ 1.60074E-7 := by
  have hr0 : 0 ≤ rhoBar 12691 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12691 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12691 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12691 BstLean.Part154.csC) (piBar (rhoBar 12691 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12691 BstLean.Part154.csC) (piBar (rhoBar 12691 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12691 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000192527427 : ℝ) ^ 2 + 0.000122506479 ^ 2 + 3 * 0.000071115948 ^ 2 +
        2 * 0.797885 * 0.000192527427 * 0.000122506479 + 2 * 0.000192527427 * 0.000071115948 +
        4 * 0.797885 * 0.000122506479 * 0.000071115948 := by gcongr
    _ ≤ (1.60074E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12691 BstLean.Part154.csC Θ ≤ 0.002631222065 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12691 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12691 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12691 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12691 BstLean.Part154.csC) (piBar (rhoBar 12691 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12691 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035822027761 * 1.60074E-7 / (0.000252062610 : ℝ) := by gcongr
    _ ≤ 0.002631222065 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12691 BstLean.Part154.csC Θ ≤ 0.002919515314 + 0.000664866498 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12691 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12691 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12691 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035822027761 : ℝ) * ((2 * Θ * 0.000252063001 +
        (6863 / 10000) * 0.000252063001 * 12691 * 0.001008315540) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002919515314 + 0.000664866498 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12691 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12691 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12691 0.011 Θ ∧ gammaRatio 12691 0.011 Θ ≤ 0.000086652742 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12691 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035822027761 : ℝ) * 0.525 / ((1 - 0.011) * 12691) := by gcongr
      _ ≤ (0.000086652742 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12691 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12691 0.011 Θ) :=
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
    badAllowance 12691 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000615501984 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12691 BstLean.Part154.csC) 1.22 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 2 (rhoBar 12691 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12691 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12691 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12691 0.011 Θ) 1.12 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 1 (gammaRatio 12691 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12691 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12691 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12691 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12691 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035822027761 : ℝ) * 12691 *
        (2.2721E-8 / 1.1045361 + 2.7751E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000615501984 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12691 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003535017298 + 0.003296088563 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12691

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12691
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12691 BstLean.Part154.csC) (piBar (rhoBar 12691 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12691 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12691 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12691 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12691 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12691 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12691 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12691 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12691 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12691 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12691 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12691 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12691 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12691 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12691 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052503121325 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12691) ≤ 0.010600901805 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12691 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035822027761)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010600901805 + 2 * 0.737676 / 12691) := by gcongr
    _ ≤ (0.052503121325 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12691 12 ≤ 0.0015 := by
  exact BstLean.Part269.S13.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12691

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12691
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560503160995 : ℝ) ≤ plow 12691 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12691) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052772063794)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001381391585) : eMP 12691 0.011 xi bn ≤ 0.001189235751 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12691 : ℝ) * (1 - 0.011))) ≤ 0.000588013498 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001381391585 / (12691 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000588013498 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000588013498 : ℝ) + 3.141593 * 0.052772063794 / (12691 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001189235751 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052772063794)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001381391585) : PiBarMP 12691 12 0.011 xi bn ≤ 0.161308778551 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12691 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037167076628 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.033026380616 : ℝ) ≤ √((12691 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.654338576017 : ℝ) ≤ √(12691 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12691) ≤ 0.123673960887 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037167076628 + 0.052772063794 * 1.772454 / (2 * (112.033026380616 : ℝ))) * (1 + 0.001189235751) +
        8 / (12691 * 112.654338576017) + 0.123673960887 := by gcongr
    _ ≤ (0.161308778551 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052772063794)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001381391585) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282224830778) :
    parallelOracle 12691 0.011 xi bn cd ≤ 0.162299988773 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12691 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12691 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560503160995 : ℝ) ≤ plow 12691 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.654338576017 : ℝ) ≤ √(12691 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282224830778 : ℝ) / (2 * 0.560503160995 * 112.654338576017)) * 0.161308778551 +
        0.282224830778 ^ 2 / (2 * 0.560503160995 * 112.654338576017) := by gcongr
    _ ≤ (0.162299988773 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052772063794) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001381391585)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282224830778) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12691 12691 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560503160995 : ℝ) ≤ plow 12691 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.654338576017 : ℝ) ≤ √(12691 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12691 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12691 Θ 1.22 ≤ 0.011771410820 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.654338576017 := by gcongr <;> linarith
      _ ≤ (0.011771410820 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12691 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12691 12691 0.011 ≤ 0.008485132875 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12691 12691 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12691 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12691 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12691 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12691 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162299988773 + 0.011771410820 + (0.008485132875 : ℝ) *
        (1 + 2 * (0.282224830778 + 0.011771410820) / (0.560503160995 * 112.654338576017))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12691]

end BstLean.Part269.N12691

/-! The original eight local profiles supply actual 12691 moment certificates. -/
namespace BstLean.Part269.N12691
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12691 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12691 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12691 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052772063794 ∧
    0 ≤ bN 12691 BstLean.Part154.csC (groupTheta g) ∧ bN 12691 BstLean.Part154.csC (groupTheta g) ≤ 0.001381391585 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12691 12691 0.011
      (momentAllowance 12691 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12691 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12691 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12691 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12691 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12691 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229721709453 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12691 0.011
      (momentAllowance 12691 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12691 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12691
/-! The actual computed-centre upper energy formula at 12691. -/
namespace BstLean.Part269.N12691
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12691

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12691
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12691)
open BstLean.Part268 (cell12691)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085516546896
  | 2 => 0.086459780176
  | 3 => 0.087401223857
  | 4 => 0.088342312289
  | 5 => 0.089284779863
  | 6 => 0.090230705496
  | 7 => 0.091182561308
  | 8 => 0.092143265495
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12691 12691 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12691 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003538895953 + 0.003300387184 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S13.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12691

/-! Actual upper energy certificates on all 43 source endpoints at 12691. -/
namespace BstLean.Part269.N12691
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12691)
open BstLean.Part268 (cell12691)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12691 (gMinus 12691) (1 - (cell12691 i).lower) ≤ 1 ∧
    energyUpper 12691 (gMinus 12691) (BstLean.Part211.gPlus 12691)
      (finiteEnergy 12691 12691 0.011) (1 - (cell12691 i).lower) ≤
      (cell12691 i).energy := by
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
      have E := BstLean.Part269.S13.uniformEnergy10 (n := 12691) (by norm_num)
        (q := 1 - (cell12691 ⟨10,by decide⟩).lower)
        (by norm_num [cell12691]) (by norm_num [cell12691])
      exact ⟨E.1,E.2.trans (by norm_num [cell12691])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy11 (n := 12691) (by norm_num)
        (q := 1 - (cell12691 ⟨11,by decide⟩).lower)
        (by norm_num [cell12691]) (by norm_num [cell12691])
      exact ⟨E.1,E.2.trans (by norm_num [cell12691])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy12 (n := 12691) (by norm_num)
        (q := 1 - (cell12691 ⟨12,by decide⟩).lower)
        (by norm_num [cell12691]) (by norm_num [cell12691])
      exact ⟨E.1,E.2.trans (by norm_num [cell12691])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy13 (n := 12691) (by norm_num)
        (q := 1 - (cell12691 ⟨13,by decide⟩).lower)
        (by norm_num [cell12691]) (by norm_num [cell12691])
      exact ⟨E.1,E.2.trans (by norm_num [cell12691])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy14 (n := 12691) (by norm_num)
        (q := 1 - (cell12691 ⟨14,by decide⟩).lower)
        (by norm_num [cell12691]) (by norm_num [cell12691])
      exact ⟨E.1,E.2.trans (by norm_num [cell12691])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy15 (n := 12691) (by norm_num)
        (q := 1 - (cell12691 ⟨15,by decide⟩).lower)
        (by norm_num [cell12691]) (by norm_num [cell12691])
      exact ⟨E.1,E.2.trans (by norm_num [cell12691])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy16 (n := 12691) (by norm_num)
        (q := 1 - (cell12691 ⟨16,by decide⟩).lower)
        (by norm_num [cell12691]) (by norm_num [cell12691])
      exact ⟨E.1,E.2.trans (by norm_num [cell12691])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy17 (n := 12691) (by norm_num)
        (q := 1 - (cell12691 ⟨17,by decide⟩).lower)
        (by norm_num [cell12691]) (by norm_num [cell12691])
      exact ⟨E.1,E.2.trans (by norm_num [cell12691])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy18 (n := 12691) (by norm_num)
        (q := 1 - (cell12691 ⟨18,by decide⟩).lower)
        (by norm_num [cell12691]) (by norm_num [cell12691])
      exact ⟨E.1,E.2.trans (by norm_num [cell12691])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy19 (n := 12691) (by norm_num)
        (q := 1 - (cell12691 ⟨19,by decide⟩).lower)
        (by norm_num [cell12691]) (by norm_num [cell12691])
      exact ⟨E.1,E.2.trans (by norm_num [cell12691])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy20 (n := 12691) (by norm_num)
        (q := 1 - (cell12691 ⟨20,by decide⟩).lower)
        (by norm_num [cell12691]) (by norm_num [cell12691])
      exact ⟨E.1,E.2.trans (by norm_num [cell12691])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy21 (n := 12691) (by norm_num)
        (q := 1 - (cell12691 ⟨21,by decide⟩).lower)
        (by norm_num [cell12691]) (by norm_num [cell12691])
      exact ⟨E.1,E.2.trans (by norm_num [cell12691])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy22 (n := 12691) (by norm_num)
        (q := 1 - (cell12691 ⟨22,by decide⟩).lower)
        (by norm_num [cell12691]) (by norm_num [cell12691])
      exact ⟨E.1,E.2.trans (by norm_num [cell12691])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy23 (n := 12691) (by norm_num)
        (q := 1 - (cell12691 ⟨23,by decide⟩).lower)
        (by norm_num [cell12691]) (by norm_num [cell12691])
      exact ⟨E.1,E.2.trans (by norm_num [cell12691])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy24 (n := 12691) (by norm_num)
        (q := 1 - (cell12691 ⟨24,by decide⟩).lower)
        (by norm_num [cell12691]) (by norm_num [cell12691])
      exact ⟨E.1,E.2.trans (by norm_num [cell12691])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy25 (n := 12691) (by norm_num)
        (q := 1 - (cell12691 ⟨25,by decide⟩).lower)
        (by norm_num [cell12691]) (by norm_num [cell12691])
      exact ⟨E.1,E.2.trans (by norm_num [cell12691])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy26 (n := 12691) (by norm_num)
        (q := 1 - (cell12691 ⟨26,by decide⟩).lower)
        (by norm_num [cell12691]) (by norm_num [cell12691])
      exact ⟨E.1,E.2.trans (by norm_num [cell12691])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy27 (n := 12691) (by norm_num)
        (q := 1 - (cell12691 ⟨27,by decide⟩).lower)
        (by norm_num [cell12691]) (by norm_num [cell12691])
      exact ⟨E.1,E.2.trans (by norm_num [cell12691])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy28 (n := 12691) (by norm_num)
        (q := 1 - (cell12691 ⟨28,by decide⟩).lower)
        (by norm_num [cell12691]) (by norm_num [cell12691])
      exact ⟨E.1,E.2.trans (by norm_num [cell12691])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy29 (n := 12691) (by norm_num)
        (q := 1 - (cell12691 ⟨29,by decide⟩).lower)
        (by norm_num [cell12691]) (by norm_num [cell12691])
      exact ⟨E.1,E.2.trans (by norm_num [cell12691])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy30 (n := 12691) (by norm_num)
        (q := 1 - (cell12691 ⟨30,by decide⟩).lower)
        (by norm_num [cell12691]) (by norm_num [cell12691])
      exact ⟨E.1,E.2.trans (by norm_num [cell12691])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy31 (n := 12691) (by norm_num)
        (q := 1 - (cell12691 ⟨31,by decide⟩).lower)
        (by norm_num [cell12691]) (by norm_num [cell12691])
      exact ⟨E.1,E.2.trans (by norm_num [cell12691])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy32 (n := 12691) (by norm_num)
        (q := 1 - (cell12691 ⟨32,by decide⟩).lower)
        (by norm_num [cell12691]) (by norm_num [cell12691])
      exact ⟨E.1,E.2.trans (by norm_num [cell12691])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy33 (n := 12691) (by norm_num)
        (q := 1 - (cell12691 ⟨33,by decide⟩).lower)
        (by norm_num [cell12691]) (by norm_num [cell12691])
      exact ⟨E.1,E.2.trans (by norm_num [cell12691])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy34 (n := 12691) (by norm_num)
        (q := 1 - (cell12691 ⟨34,by decide⟩).lower)
        (by norm_num [cell12691]) (by norm_num [cell12691])
      exact ⟨E.1,E.2.trans (by norm_num [cell12691])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy35 (n := 12691) (by norm_num)
        (q := 1 - (cell12691 ⟨35,by decide⟩).lower)
        (by norm_num [cell12691]) (by norm_num [cell12691])
      exact ⟨E.1,E.2.trans (by norm_num [cell12691])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy36 (n := 12691) (by norm_num)
        (q := 1 - (cell12691 ⟨36,by decide⟩).lower)
        (by norm_num [cell12691]) (by norm_num [cell12691])
      exact ⟨E.1,E.2.trans (by norm_num [cell12691])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy37 (n := 12691) (by norm_num)
        (q := 1 - (cell12691 ⟨37,by decide⟩).lower)
        (by norm_num [cell12691]) (by norm_num [cell12691])
      exact ⟨E.1,E.2.trans (by norm_num [cell12691])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy38 (n := 12691) (by norm_num)
        (q := 1 - (cell12691 ⟨38,by decide⟩).lower)
        (by norm_num [cell12691]) (by norm_num [cell12691])
      exact ⟨E.1,E.2.trans (by norm_num [cell12691])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy39 (n := 12691) (by norm_num)
        (q := 1 - (cell12691 ⟨39,by decide⟩).lower)
        (by norm_num [cell12691]) (by norm_num [cell12691])
      exact ⟨E.1,E.2.trans (by norm_num [cell12691])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy40 (n := 12691) (by norm_num)
        (q := 1 - (cell12691 ⟨40,by decide⟩).lower)
        (by norm_num [cell12691]) (by norm_num [cell12691])
      exact ⟨E.1,E.2.trans (by norm_num [cell12691])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy41 (n := 12691) (by norm_num)
        (q := 1 - (cell12691 ⟨41,by decide⟩).lower)
        (by norm_num [cell12691]) (by norm_num [cell12691])
      exact ⟨E.1,E.2.trans (by norm_num [cell12691])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy42 (n := 12691) (by norm_num)
        (q := 1 - (cell12691 ⟨42,by decide⟩).lower)
        (by norm_num [cell12691]) (by norm_num [cell12691])
      exact ⟨E.1,E.2.trans (by norm_num [cell12691])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy43 (n := 12691) (by norm_num)
        (q := 1 - (cell12691 ⟨43,by decide⟩).lower)
        (by norm_num [cell12691]) (by norm_num [cell12691])
      exact ⟨E.1,E.2.trans (by norm_num [cell12691])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy44 (n := 12691) (by norm_num)
        (q := 1 - (cell12691 ⟨44,by decide⟩).lower)
        (by norm_num [cell12691]) (by norm_num [cell12691])
      exact ⟨E.1,E.2.trans (by norm_num [cell12691])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy45 (n := 12691) (by norm_num)
        (q := 1 - (cell12691 ⟨45,by decide⟩).lower)
        (by norm_num [cell12691]) (by norm_num [cell12691])
      exact ⟨E.1,E.2.trans (by norm_num [cell12691])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy46 (n := 12691) (by norm_num)
        (q := 1 - (cell12691 ⟨46,by decide⟩).lower)
        (by norm_num [cell12691]) (by norm_num [cell12691])
      exact ⟨E.1,E.2.trans (by norm_num [cell12691])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy47 (n := 12691) (by norm_num)
        (q := 1 - (cell12691 ⟨47,by decide⟩).lower)
        (by norm_num [cell12691]) (by norm_num [cell12691])
      exact ⟨E.1,E.2.trans (by norm_num [cell12691])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy48 (n := 12691) (by norm_num)
        (q := 1 - (cell12691 ⟨48,by decide⟩).lower)
        (by norm_num [cell12691]) (by norm_num [cell12691])
      exact ⟨E.1,E.2.trans (by norm_num [cell12691])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy49 (n := 12691) (by norm_num)
        (q := 1 - (cell12691 ⟨49,by decide⟩).lower)
        (by norm_num [cell12691]) (by norm_num [cell12691])
      exact ⟨E.1,E.2.trans (by norm_num [cell12691])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy50 (n := 12691) (by norm_num)
        (q := 1 - (cell12691 ⟨50,by decide⟩).lower)
        (by norm_num [cell12691]) (by norm_num [cell12691])
      exact ⟨E.1,E.2.trans (by norm_num [cell12691])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy51 (n := 12691) (by norm_num)
        (q := 1 - (cell12691 ⟨51,by decide⟩).lower)
        (by norm_num [cell12691]) (by norm_num [cell12691])
      exact ⟨E.1,E.2.trans (by norm_num [cell12691])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy52 (n := 12691) (by norm_num)
        (q := 1 - (cell12691 ⟨52,by decide⟩).lower)
        (by norm_num [cell12691]) (by norm_num [cell12691])
      exact ⟨E.1,E.2.trans (by norm_num [cell12691])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12691

/-! Source-cell containment and simple scalar guards at 12691. -/
namespace BstLean.Part269.N12691
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12691)
open BstLean.Part268 (cell12691)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12691 ⟨10,by decide⟩).lower ∧ (cell12691 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12691 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12691 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12691 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12691 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12691 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12691,cell12691,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12691 ⟨11,by decide⟩).lower ∧ (cell12691 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12691 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12691 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12691 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12691 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12691 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12691,cell12691,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12691 ⟨12,by decide⟩).lower ∧ (cell12691 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12691 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12691 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12691 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12691 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12691 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12691,cell12691,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12691 ⟨13,by decide⟩).lower ∧ (cell12691 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12691 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12691 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12691 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12691 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12691 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12691,cell12691,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12691 ⟨14,by decide⟩).lower ∧ (cell12691 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12691 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12691 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12691 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12691 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12691 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12691,cell12691,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12691 ⟨15,by decide⟩).lower ∧ (cell12691 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12691 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12691 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12691 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12691 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12691 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12691,cell12691,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12691 ⟨16,by decide⟩).lower ∧ (cell12691 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12691 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12691 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12691 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12691 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12691 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12691,cell12691,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12691 ⟨17,by decide⟩).lower ∧ (cell12691 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12691 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12691 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12691 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12691 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12691 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12691,cell12691,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12691 ⟨18,by decide⟩).lower ∧ (cell12691 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12691 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12691 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12691 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12691 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12691 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12691,cell12691,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12691 ⟨19,by decide⟩).lower ∧ (cell12691 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12691 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12691 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12691 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12691 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12691 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12691,cell12691,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12691 ⟨20,by decide⟩).lower ∧ (cell12691 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12691 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12691 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12691 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12691 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12691 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12691,cell12691,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12691 ⟨21,by decide⟩).lower ∧ (cell12691 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12691 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12691 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12691 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12691 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12691 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12691,cell12691,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12691 ⟨22,by decide⟩).lower ∧ (cell12691 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12691 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12691 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12691 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12691 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12691 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12691,cell12691,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12691 ⟨23,by decide⟩).lower ∧ (cell12691 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12691 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12691 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12691 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12691 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12691 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12691,cell12691,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12691 ⟨24,by decide⟩).lower ∧ (cell12691 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12691 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12691 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12691 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12691 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12691 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12691,cell12691,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12691 ⟨25,by decide⟩).lower ∧ (cell12691 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12691 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12691 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12691 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12691 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12691 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12691,cell12691,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12691 ⟨26,by decide⟩).lower ∧ (cell12691 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12691 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12691 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12691 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12691 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12691 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12691,cell12691,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12691 ⟨27,by decide⟩).lower ∧ (cell12691 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12691 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12691 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12691 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12691 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12691 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12691,cell12691,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12691 ⟨28,by decide⟩).lower ∧ (cell12691 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12691 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12691 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12691 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12691 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12691 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12691,cell12691,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12691 ⟨29,by decide⟩).lower ∧ (cell12691 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12691 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12691 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12691 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12691 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12691 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12691,cell12691,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12691 ⟨30,by decide⟩).lower ∧ (cell12691 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12691 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12691 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12691 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12691 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12691 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12691,cell12691,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12691 ⟨31,by decide⟩).lower ∧ (cell12691 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12691 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12691 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12691 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12691 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12691 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12691,cell12691,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12691 ⟨32,by decide⟩).lower ∧ (cell12691 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12691 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12691 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12691 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12691 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12691 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12691,cell12691,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12691 ⟨33,by decide⟩).lower ∧ (cell12691 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12691 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12691 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12691 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12691 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12691 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12691,cell12691,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12691 ⟨34,by decide⟩).lower ∧ (cell12691 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12691 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12691 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12691 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12691 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12691 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12691,cell12691,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12691 ⟨35,by decide⟩).lower ∧ (cell12691 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12691 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12691 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12691 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12691 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12691 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12691,cell12691,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12691 ⟨36,by decide⟩).lower ∧ (cell12691 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12691 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12691 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12691 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12691 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12691 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12691,cell12691,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12691 ⟨37,by decide⟩).lower ∧ (cell12691 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12691 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12691 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12691 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12691 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12691 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12691,cell12691,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12691 ⟨38,by decide⟩).lower ∧ (cell12691 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12691 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12691 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12691 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12691 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12691 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12691,cell12691,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12691 ⟨39,by decide⟩).lower ∧ (cell12691 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12691 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12691 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12691 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12691 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12691 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12691,cell12691,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12691 ⟨40,by decide⟩).lower ∧ (cell12691 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12691 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12691 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12691 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12691 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12691 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12691,cell12691,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12691 ⟨41,by decide⟩).lower ∧ (cell12691 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12691 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12691 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12691 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12691 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12691 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12691,cell12691,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12691 ⟨42,by decide⟩).lower ∧ (cell12691 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12691 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12691 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12691 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12691 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12691 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12691,cell12691,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12691 ⟨43,by decide⟩).lower ∧ (cell12691 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12691 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12691 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12691 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12691 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12691 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12691,cell12691,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12691 ⟨44,by decide⟩).lower ∧ (cell12691 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12691 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12691 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12691 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12691 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12691 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12691,cell12691,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12691 ⟨45,by decide⟩).lower ∧ (cell12691 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12691 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12691 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12691 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12691 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12691 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12691,cell12691,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12691 ⟨46,by decide⟩).lower ∧ (cell12691 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12691 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12691 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12691 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12691 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12691 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12691,cell12691,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12691 ⟨47,by decide⟩).lower ∧ (cell12691 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12691 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12691 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12691 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12691 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12691 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12691,cell12691,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12691 ⟨48,by decide⟩).lower ∧ (cell12691 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12691 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12691 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12691 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12691 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12691 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12691,cell12691,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12691 ⟨49,by decide⟩).lower ∧ (cell12691 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12691 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12691 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12691 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12691 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12691 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12691,cell12691,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12691 ⟨50,by decide⟩).lower ∧ (cell12691 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12691 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12691 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12691 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12691 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12691 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12691,cell12691,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12691 ⟨51,by decide⟩).lower ∧ (cell12691 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12691 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12691 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12691 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12691 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12691 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12691,cell12691,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12691 ⟨52,by decide⟩).lower ∧ (cell12691 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12691 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12691 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12691 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12691 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12691 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12691,cell12691,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12691 i).lower ∧
    (cell12691 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12691 i).upper ≤ (0.532 : ℝ) ∧
    (cell12691 i).centre ≤ (0.1 : ℝ) ∧ (cell12691 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12691 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12691 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12691

/-! The local source numeric instances at 12691 have no network premises. -/
namespace BstLean.Part269.N12691
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12691)
open BstLean.Part268 (cell12691)

noncomputable def sourceNumerics12691 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12691 (cell12691 i)
      scalarRow12691.M scalarRow12691.H scalarRow12691.xi := by
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
    energy_allowance := scalarRow12691.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12691]
    centre_nonneg := (scalarRow12691.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D13.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12691])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12691
/-! Actual 12692 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12692
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12692 ≤ (1.035820604111 : ℝ) := by
  have hr : (112.658776844061 : ℝ) ≤ √(12692 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.658776844061 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12692 12692 (11 / 1000) ≤
    (0.008484798595 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12692) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.658776844061 : ℝ) ≤ √(12692 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12692)
  have hdiv : K / √(12692 : ℝ) ≤ K / 112.658776844061 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.658776844061 ≤ (0.008484798595 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12692.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12692 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12692 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12692 := gPlus_lower 12692
end BstLean.Part269.N12692

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12692
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035820604110 : ℝ) ≤ wn 12692 := by
  have hn : √(12692 : ℝ) ≤ 112.658776844062 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12692 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.658776844062 ≤ 2 / √(12692 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000252042404 : ℝ) ≤ rhoBar 12692 BstLean.Part154.csC ∧
    rhoBar 12692 BstLean.Part154.csC ≤ 0.000252042794 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035820604110 : ℝ) / (1.295212 * 12692) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035820604111 : ℝ) / (1.29521 * 12692) := by gcongr
      _ ≤ (0.000252042794 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12692 BstLean.Part154.csC) ≤ 0.001008234702 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12692 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12692 BstLean.Part154.csC) (piBar (rhoBar 12692 BstLean.Part154.csC)) ≤ 0.000192511992 ∧
    cc1 (rhoBar 12692 BstLean.Part154.csC) (piBar (rhoBar 12692 BstLean.Part154.csC)) ≤ 0.000122496658 ∧
    cc2 (rhoBar 12692 BstLean.Part154.csC) ≤ 0.000071110247 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12692 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12692 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12692 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12692 BstLean.Part154.csC * nuR (rhoBar 12692 BstLean.Part154.csC)) ≤ 0.000504101470 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000252042794 : ℝ) * 0.001008234702 := by gcongr
      _ ≤ (0.000504101470 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12692 BstLean.Part154.csC) * nuR (rhoBar 12692 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001008234702 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12692 BstLean.Part154.csC) * rhoBar 12692 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000252042794 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000252042794 / 2 + 0.399 * 0.001008234702 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000192511992 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000504101470 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122496658 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000252042794 / 1.414213562 := by gcongr
      _ ≤ (0.000071110247 : ℝ) := by norm_num

end BstLean.Part269.N12692

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12692
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12692 BstLean.Part154.csC) (piBar (rhoBar 12692 BstLean.Part154.csC)) ≤ 1.60048E-7 := by
  have hr0 : 0 ≤ rhoBar 12692 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12692 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12692 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12692 BstLean.Part154.csC) (piBar (rhoBar 12692 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12692 BstLean.Part154.csC) (piBar (rhoBar 12692 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12692 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000192511992 : ℝ) ^ 2 + 0.000122496658 ^ 2 + 3 * 0.000071110247 ^ 2 +
        2 * 0.797885 * 0.000192511992 * 0.000122496658 + 2 * 0.000192511992 * 0.000071110247 +
        4 * 0.797885 * 0.000122496658 * 0.000071110247 := by gcongr
    _ ≤ (1.60048E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12692 BstLean.Part154.csC Θ ≤ 0.002631001981 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12692 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12692 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12692 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12692 BstLean.Part154.csC) (piBar (rhoBar 12692 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12692 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035820604111 * 1.60048E-7 / (0.000252042404 : ℝ) := by gcongr
    _ ≤ 0.002631001981 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12692 BstLean.Part154.csC Θ ≤ 0.002919273221 + 0.000664812285 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12692 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12692 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12692 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035820604111 : ℝ) * ((2 * Θ * 0.000252042794 +
        (6863 / 10000) * 0.000252042794 * 12692 * 0.001008234702) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002919273221 + 0.000664812285 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12692 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12692 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12692 0.011 Θ ∧ gammaRatio 12692 0.011 Θ ≤ 0.000086645795 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12692 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035820604111 : ℝ) * 0.525 / ((1 - 0.011) * 12692) := by gcongr
      _ ≤ (0.000086645795 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12692 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12692 0.011 Θ) :=
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
    badAllowance 12692 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000615501984 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12692 BstLean.Part154.csC) 1.22 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 2 (rhoBar 12692 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12692 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12692 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12692 0.011 Θ) 1.12 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 1 (gammaRatio 12692 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12692 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12692 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12692 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12692 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035820604111 : ℝ) * 12692 *
        (2.2721E-8 / 1.1045361 + 2.7751E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000615501984 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12692 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003534775205 + 0.003295814266 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12692

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12692
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12692 BstLean.Part154.csC) (piBar (rhoBar 12692 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12692 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12692 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12692 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12692 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12692 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12692 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12692 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12692 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12692 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12692 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12692 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12692 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12692 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12692 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052501030492 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12692) ≤ 0.010600484175 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12692 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035820604111)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010600484175 + 2 * 0.737676 / 12692) := by gcongr
    _ ≤ (0.052501030492 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12692 12 ≤ 0.0015 := by
  exact BstLean.Part269.S13.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12692

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12692
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560503206279 : ℝ) ≤ plow 12692 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12692) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052771677695)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001381276041) : eMP 12692 0.011 xi bn ≤ 0.001189139102 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12692 : ℝ) * (1 - 0.011))) ≤ 0.000587965742 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001381276041 / (12692 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000587965742 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000587965742 : ℝ) + 3.141593 * 0.052771677695 / (12692 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001189139102 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052771677695)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001381276041) : PiBarMP 12692 12 0.011 xi bn ≤ 0.161302326248 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12692 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037165522209 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.037440170685 : ℝ) ≤ √((12692 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.658776844061 : ℝ) ≤ √(12692 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12692) ≤ 0.123669088668 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037165522209 + 0.052771677695 * 1.772454 / (2 * (112.037440170685 : ℝ))) * (1 + 0.001189139102) +
        8 / (12692 * 112.658776844061) + 0.123669088668 := by gcongr
    _ ≤ (0.161302326248 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052771677695)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001381276041) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282221899581) :
    parallelOracle 12692 0.011 xi bn cd ≤ 0.162293466077 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12692 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12692 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560503206279 : ℝ) ≤ plow 12692 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.658776844061 : ℝ) ≤ √(12692 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282221899581 : ℝ) / (2 * 0.560503206279 * 112.658776844061)) * 0.161302326248 +
        0.282221899581 ^ 2 / (2 * 0.560503206279 * 112.658776844061) := by gcongr
    _ ≤ (0.162293466077 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052771677695) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001381276041)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282221899581) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12692 12692 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560503206279 : ℝ) ≤ plow 12692 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.658776844061 : ℝ) ≤ √(12692 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12692 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12692 Θ 1.22 ≤ 0.011770947078 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.658776844061 := by gcongr <;> linarith
      _ ≤ (0.011770947078 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12692 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12692 12692 0.011 ≤ 0.008484798595 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12692 12692 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12692 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12692 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12692 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12692 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162293466077 + 0.011770947078 + (0.008484798595 : ℝ) *
        (1 + 2 * (0.282221899581 + 0.011770947078) / (0.560503206279 * 112.658776844061))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12692]

end BstLean.Part269.N12692

/-! The original eight local profiles supply actual 12692 moment certificates. -/
namespace BstLean.Part269.N12692
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12692 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12692 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12692 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052771677695 ∧
    0 ≤ bN 12692 BstLean.Part154.csC (groupTheta g) ∧ bN 12692 BstLean.Part154.csC (groupTheta g) ≤ 0.001381276041 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12692 12692 0.011
      (momentAllowance 12692 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12692 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12692 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12692 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12692 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12692 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229720869089 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12692 0.011
      (momentAllowance 12692 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12692 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12692
/-! The actual computed-centre upper energy formula at 12692. -/
namespace BstLean.Part269.N12692
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12692

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12692
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12692)
open BstLean.Part268 (cell12692)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085513621348
  | 2 => 0.086456800670
  | 3 => 0.087398182485
  | 4 => 0.088339199330
  | 5 => 0.089281583451
  | 6 => 0.090227411268
  | 7 => 0.091179151998
  | 8 => 0.092139720488
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12692 12692 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12692 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003538895953 + 0.003300387184 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S13.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12692

/-! Actual upper energy certificates on all 43 source endpoints at 12692. -/
namespace BstLean.Part269.N12692
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12692)
open BstLean.Part268 (cell12692)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12692 (gMinus 12692) (1 - (cell12692 i).lower) ≤ 1 ∧
    energyUpper 12692 (gMinus 12692) (BstLean.Part211.gPlus 12692)
      (finiteEnergy 12692 12692 0.011) (1 - (cell12692 i).lower) ≤
      (cell12692 i).energy := by
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
      have E := BstLean.Part269.S13.uniformEnergy10 (n := 12692) (by norm_num)
        (q := 1 - (cell12692 ⟨10,by decide⟩).lower)
        (by norm_num [cell12692]) (by norm_num [cell12692])
      exact ⟨E.1,E.2.trans (by norm_num [cell12692])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy11 (n := 12692) (by norm_num)
        (q := 1 - (cell12692 ⟨11,by decide⟩).lower)
        (by norm_num [cell12692]) (by norm_num [cell12692])
      exact ⟨E.1,E.2.trans (by norm_num [cell12692])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy12 (n := 12692) (by norm_num)
        (q := 1 - (cell12692 ⟨12,by decide⟩).lower)
        (by norm_num [cell12692]) (by norm_num [cell12692])
      exact ⟨E.1,E.2.trans (by norm_num [cell12692])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy13 (n := 12692) (by norm_num)
        (q := 1 - (cell12692 ⟨13,by decide⟩).lower)
        (by norm_num [cell12692]) (by norm_num [cell12692])
      exact ⟨E.1,E.2.trans (by norm_num [cell12692])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy14 (n := 12692) (by norm_num)
        (q := 1 - (cell12692 ⟨14,by decide⟩).lower)
        (by norm_num [cell12692]) (by norm_num [cell12692])
      exact ⟨E.1,E.2.trans (by norm_num [cell12692])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy15 (n := 12692) (by norm_num)
        (q := 1 - (cell12692 ⟨15,by decide⟩).lower)
        (by norm_num [cell12692]) (by norm_num [cell12692])
      exact ⟨E.1,E.2.trans (by norm_num [cell12692])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy16 (n := 12692) (by norm_num)
        (q := 1 - (cell12692 ⟨16,by decide⟩).lower)
        (by norm_num [cell12692]) (by norm_num [cell12692])
      exact ⟨E.1,E.2.trans (by norm_num [cell12692])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy17 (n := 12692) (by norm_num)
        (q := 1 - (cell12692 ⟨17,by decide⟩).lower)
        (by norm_num [cell12692]) (by norm_num [cell12692])
      exact ⟨E.1,E.2.trans (by norm_num [cell12692])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy18 (n := 12692) (by norm_num)
        (q := 1 - (cell12692 ⟨18,by decide⟩).lower)
        (by norm_num [cell12692]) (by norm_num [cell12692])
      exact ⟨E.1,E.2.trans (by norm_num [cell12692])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy19 (n := 12692) (by norm_num)
        (q := 1 - (cell12692 ⟨19,by decide⟩).lower)
        (by norm_num [cell12692]) (by norm_num [cell12692])
      exact ⟨E.1,E.2.trans (by norm_num [cell12692])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy20 (n := 12692) (by norm_num)
        (q := 1 - (cell12692 ⟨20,by decide⟩).lower)
        (by norm_num [cell12692]) (by norm_num [cell12692])
      exact ⟨E.1,E.2.trans (by norm_num [cell12692])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy21 (n := 12692) (by norm_num)
        (q := 1 - (cell12692 ⟨21,by decide⟩).lower)
        (by norm_num [cell12692]) (by norm_num [cell12692])
      exact ⟨E.1,E.2.trans (by norm_num [cell12692])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy22 (n := 12692) (by norm_num)
        (q := 1 - (cell12692 ⟨22,by decide⟩).lower)
        (by norm_num [cell12692]) (by norm_num [cell12692])
      exact ⟨E.1,E.2.trans (by norm_num [cell12692])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy23 (n := 12692) (by norm_num)
        (q := 1 - (cell12692 ⟨23,by decide⟩).lower)
        (by norm_num [cell12692]) (by norm_num [cell12692])
      exact ⟨E.1,E.2.trans (by norm_num [cell12692])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy24 (n := 12692) (by norm_num)
        (q := 1 - (cell12692 ⟨24,by decide⟩).lower)
        (by norm_num [cell12692]) (by norm_num [cell12692])
      exact ⟨E.1,E.2.trans (by norm_num [cell12692])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy25 (n := 12692) (by norm_num)
        (q := 1 - (cell12692 ⟨25,by decide⟩).lower)
        (by norm_num [cell12692]) (by norm_num [cell12692])
      exact ⟨E.1,E.2.trans (by norm_num [cell12692])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy26 (n := 12692) (by norm_num)
        (q := 1 - (cell12692 ⟨26,by decide⟩).lower)
        (by norm_num [cell12692]) (by norm_num [cell12692])
      exact ⟨E.1,E.2.trans (by norm_num [cell12692])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy27 (n := 12692) (by norm_num)
        (q := 1 - (cell12692 ⟨27,by decide⟩).lower)
        (by norm_num [cell12692]) (by norm_num [cell12692])
      exact ⟨E.1,E.2.trans (by norm_num [cell12692])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy28 (n := 12692) (by norm_num)
        (q := 1 - (cell12692 ⟨28,by decide⟩).lower)
        (by norm_num [cell12692]) (by norm_num [cell12692])
      exact ⟨E.1,E.2.trans (by norm_num [cell12692])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy29 (n := 12692) (by norm_num)
        (q := 1 - (cell12692 ⟨29,by decide⟩).lower)
        (by norm_num [cell12692]) (by norm_num [cell12692])
      exact ⟨E.1,E.2.trans (by norm_num [cell12692])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy30 (n := 12692) (by norm_num)
        (q := 1 - (cell12692 ⟨30,by decide⟩).lower)
        (by norm_num [cell12692]) (by norm_num [cell12692])
      exact ⟨E.1,E.2.trans (by norm_num [cell12692])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy31 (n := 12692) (by norm_num)
        (q := 1 - (cell12692 ⟨31,by decide⟩).lower)
        (by norm_num [cell12692]) (by norm_num [cell12692])
      exact ⟨E.1,E.2.trans (by norm_num [cell12692])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy32 (n := 12692) (by norm_num)
        (q := 1 - (cell12692 ⟨32,by decide⟩).lower)
        (by norm_num [cell12692]) (by norm_num [cell12692])
      exact ⟨E.1,E.2.trans (by norm_num [cell12692])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy33 (n := 12692) (by norm_num)
        (q := 1 - (cell12692 ⟨33,by decide⟩).lower)
        (by norm_num [cell12692]) (by norm_num [cell12692])
      exact ⟨E.1,E.2.trans (by norm_num [cell12692])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy34 (n := 12692) (by norm_num)
        (q := 1 - (cell12692 ⟨34,by decide⟩).lower)
        (by norm_num [cell12692]) (by norm_num [cell12692])
      exact ⟨E.1,E.2.trans (by norm_num [cell12692])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy35 (n := 12692) (by norm_num)
        (q := 1 - (cell12692 ⟨35,by decide⟩).lower)
        (by norm_num [cell12692]) (by norm_num [cell12692])
      exact ⟨E.1,E.2.trans (by norm_num [cell12692])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy36 (n := 12692) (by norm_num)
        (q := 1 - (cell12692 ⟨36,by decide⟩).lower)
        (by norm_num [cell12692]) (by norm_num [cell12692])
      exact ⟨E.1,E.2.trans (by norm_num [cell12692])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy37 (n := 12692) (by norm_num)
        (q := 1 - (cell12692 ⟨37,by decide⟩).lower)
        (by norm_num [cell12692]) (by norm_num [cell12692])
      exact ⟨E.1,E.2.trans (by norm_num [cell12692])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy38 (n := 12692) (by norm_num)
        (q := 1 - (cell12692 ⟨38,by decide⟩).lower)
        (by norm_num [cell12692]) (by norm_num [cell12692])
      exact ⟨E.1,E.2.trans (by norm_num [cell12692])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy39 (n := 12692) (by norm_num)
        (q := 1 - (cell12692 ⟨39,by decide⟩).lower)
        (by norm_num [cell12692]) (by norm_num [cell12692])
      exact ⟨E.1,E.2.trans (by norm_num [cell12692])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy40 (n := 12692) (by norm_num)
        (q := 1 - (cell12692 ⟨40,by decide⟩).lower)
        (by norm_num [cell12692]) (by norm_num [cell12692])
      exact ⟨E.1,E.2.trans (by norm_num [cell12692])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy41 (n := 12692) (by norm_num)
        (q := 1 - (cell12692 ⟨41,by decide⟩).lower)
        (by norm_num [cell12692]) (by norm_num [cell12692])
      exact ⟨E.1,E.2.trans (by norm_num [cell12692])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy42 (n := 12692) (by norm_num)
        (q := 1 - (cell12692 ⟨42,by decide⟩).lower)
        (by norm_num [cell12692]) (by norm_num [cell12692])
      exact ⟨E.1,E.2.trans (by norm_num [cell12692])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy43 (n := 12692) (by norm_num)
        (q := 1 - (cell12692 ⟨43,by decide⟩).lower)
        (by norm_num [cell12692]) (by norm_num [cell12692])
      exact ⟨E.1,E.2.trans (by norm_num [cell12692])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy44 (n := 12692) (by norm_num)
        (q := 1 - (cell12692 ⟨44,by decide⟩).lower)
        (by norm_num [cell12692]) (by norm_num [cell12692])
      exact ⟨E.1,E.2.trans (by norm_num [cell12692])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy45 (n := 12692) (by norm_num)
        (q := 1 - (cell12692 ⟨45,by decide⟩).lower)
        (by norm_num [cell12692]) (by norm_num [cell12692])
      exact ⟨E.1,E.2.trans (by norm_num [cell12692])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy46 (n := 12692) (by norm_num)
        (q := 1 - (cell12692 ⟨46,by decide⟩).lower)
        (by norm_num [cell12692]) (by norm_num [cell12692])
      exact ⟨E.1,E.2.trans (by norm_num [cell12692])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy47 (n := 12692) (by norm_num)
        (q := 1 - (cell12692 ⟨47,by decide⟩).lower)
        (by norm_num [cell12692]) (by norm_num [cell12692])
      exact ⟨E.1,E.2.trans (by norm_num [cell12692])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy48 (n := 12692) (by norm_num)
        (q := 1 - (cell12692 ⟨48,by decide⟩).lower)
        (by norm_num [cell12692]) (by norm_num [cell12692])
      exact ⟨E.1,E.2.trans (by norm_num [cell12692])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy49 (n := 12692) (by norm_num)
        (q := 1 - (cell12692 ⟨49,by decide⟩).lower)
        (by norm_num [cell12692]) (by norm_num [cell12692])
      exact ⟨E.1,E.2.trans (by norm_num [cell12692])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy50 (n := 12692) (by norm_num)
        (q := 1 - (cell12692 ⟨50,by decide⟩).lower)
        (by norm_num [cell12692]) (by norm_num [cell12692])
      exact ⟨E.1,E.2.trans (by norm_num [cell12692])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy51 (n := 12692) (by norm_num)
        (q := 1 - (cell12692 ⟨51,by decide⟩).lower)
        (by norm_num [cell12692]) (by norm_num [cell12692])
      exact ⟨E.1,E.2.trans (by norm_num [cell12692])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy52 (n := 12692) (by norm_num)
        (q := 1 - (cell12692 ⟨52,by decide⟩).lower)
        (by norm_num [cell12692]) (by norm_num [cell12692])
      exact ⟨E.1,E.2.trans (by norm_num [cell12692])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12692

/-! Source-cell containment and simple scalar guards at 12692. -/
namespace BstLean.Part269.N12692
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12692)
open BstLean.Part268 (cell12692)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12692 ⟨10,by decide⟩).lower ∧ (cell12692 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12692 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12692 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12692 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12692 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12692 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12692,cell12692,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12692 ⟨11,by decide⟩).lower ∧ (cell12692 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12692 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12692 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12692 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12692 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12692 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12692,cell12692,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12692 ⟨12,by decide⟩).lower ∧ (cell12692 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12692 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12692 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12692 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12692 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12692 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12692,cell12692,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12692 ⟨13,by decide⟩).lower ∧ (cell12692 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12692 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12692 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12692 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12692 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12692 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12692,cell12692,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12692 ⟨14,by decide⟩).lower ∧ (cell12692 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12692 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12692 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12692 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12692 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12692 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12692,cell12692,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12692 ⟨15,by decide⟩).lower ∧ (cell12692 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12692 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12692 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12692 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12692 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12692 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12692,cell12692,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12692 ⟨16,by decide⟩).lower ∧ (cell12692 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12692 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12692 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12692 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12692 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12692 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12692,cell12692,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12692 ⟨17,by decide⟩).lower ∧ (cell12692 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12692 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12692 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12692 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12692 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12692 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12692,cell12692,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12692 ⟨18,by decide⟩).lower ∧ (cell12692 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12692 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12692 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12692 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12692 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12692 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12692,cell12692,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12692 ⟨19,by decide⟩).lower ∧ (cell12692 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12692 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12692 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12692 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12692 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12692 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12692,cell12692,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12692 ⟨20,by decide⟩).lower ∧ (cell12692 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12692 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12692 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12692 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12692 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12692 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12692,cell12692,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12692 ⟨21,by decide⟩).lower ∧ (cell12692 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12692 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12692 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12692 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12692 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12692 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12692,cell12692,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12692 ⟨22,by decide⟩).lower ∧ (cell12692 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12692 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12692 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12692 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12692 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12692 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12692,cell12692,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12692 ⟨23,by decide⟩).lower ∧ (cell12692 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12692 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12692 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12692 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12692 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12692 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12692,cell12692,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12692 ⟨24,by decide⟩).lower ∧ (cell12692 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12692 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12692 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12692 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12692 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12692 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12692,cell12692,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12692 ⟨25,by decide⟩).lower ∧ (cell12692 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12692 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12692 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12692 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12692 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12692 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12692,cell12692,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12692 ⟨26,by decide⟩).lower ∧ (cell12692 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12692 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12692 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12692 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12692 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12692 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12692,cell12692,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12692 ⟨27,by decide⟩).lower ∧ (cell12692 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12692 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12692 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12692 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12692 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12692 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12692,cell12692,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12692 ⟨28,by decide⟩).lower ∧ (cell12692 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12692 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12692 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12692 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12692 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12692 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12692,cell12692,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12692 ⟨29,by decide⟩).lower ∧ (cell12692 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12692 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12692 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12692 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12692 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12692 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12692,cell12692,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12692 ⟨30,by decide⟩).lower ∧ (cell12692 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12692 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12692 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12692 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12692 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12692 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12692,cell12692,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12692 ⟨31,by decide⟩).lower ∧ (cell12692 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12692 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12692 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12692 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12692 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12692 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12692,cell12692,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12692 ⟨32,by decide⟩).lower ∧ (cell12692 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12692 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12692 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12692 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12692 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12692 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12692,cell12692,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12692 ⟨33,by decide⟩).lower ∧ (cell12692 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12692 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12692 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12692 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12692 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12692 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12692,cell12692,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12692 ⟨34,by decide⟩).lower ∧ (cell12692 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12692 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12692 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12692 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12692 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12692 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12692,cell12692,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12692 ⟨35,by decide⟩).lower ∧ (cell12692 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12692 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12692 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12692 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12692 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12692 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12692,cell12692,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12692 ⟨36,by decide⟩).lower ∧ (cell12692 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12692 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12692 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12692 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12692 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12692 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12692,cell12692,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12692 ⟨37,by decide⟩).lower ∧ (cell12692 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12692 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12692 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12692 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12692 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12692 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12692,cell12692,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12692 ⟨38,by decide⟩).lower ∧ (cell12692 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12692 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12692 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12692 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12692 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12692 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12692,cell12692,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12692 ⟨39,by decide⟩).lower ∧ (cell12692 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12692 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12692 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12692 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12692 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12692 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12692,cell12692,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12692 ⟨40,by decide⟩).lower ∧ (cell12692 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12692 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12692 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12692 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12692 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12692 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12692,cell12692,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12692 ⟨41,by decide⟩).lower ∧ (cell12692 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12692 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12692 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12692 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12692 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12692 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12692,cell12692,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12692 ⟨42,by decide⟩).lower ∧ (cell12692 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12692 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12692 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12692 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12692 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12692 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12692,cell12692,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12692 ⟨43,by decide⟩).lower ∧ (cell12692 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12692 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12692 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12692 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12692 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12692 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12692,cell12692,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12692 ⟨44,by decide⟩).lower ∧ (cell12692 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12692 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12692 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12692 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12692 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12692 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12692,cell12692,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12692 ⟨45,by decide⟩).lower ∧ (cell12692 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12692 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12692 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12692 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12692 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12692 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12692,cell12692,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12692 ⟨46,by decide⟩).lower ∧ (cell12692 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12692 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12692 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12692 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12692 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12692 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12692,cell12692,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12692 ⟨47,by decide⟩).lower ∧ (cell12692 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12692 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12692 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12692 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12692 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12692 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12692,cell12692,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12692 ⟨48,by decide⟩).lower ∧ (cell12692 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12692 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12692 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12692 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12692 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12692 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12692,cell12692,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12692 ⟨49,by decide⟩).lower ∧ (cell12692 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12692 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12692 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12692 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12692 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12692 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12692,cell12692,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12692 ⟨50,by decide⟩).lower ∧ (cell12692 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12692 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12692 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12692 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12692 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12692 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12692,cell12692,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12692 ⟨51,by decide⟩).lower ∧ (cell12692 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12692 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12692 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12692 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12692 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12692 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12692,cell12692,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12692 ⟨52,by decide⟩).lower ∧ (cell12692 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12692 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12692 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12692 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12692 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12692 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12692,cell12692,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12692 i).lower ∧
    (cell12692 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12692 i).upper ≤ (0.532 : ℝ) ∧
    (cell12692 i).centre ≤ (0.1 : ℝ) ∧ (cell12692 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12692 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12692 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12692

/-! The local source numeric instances at 12692 have no network premises. -/
namespace BstLean.Part269.N12692
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12692)
open BstLean.Part268 (cell12692)

noncomputable def sourceNumerics12692 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12692 (cell12692 i)
      scalarRow12692.M scalarRow12692.H scalarRow12692.xi := by
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
    energy_allowance := scalarRow12692.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12692]
    centre_nonneg := (scalarRow12692.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D13.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12692])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12692
/-! Actual 12693 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12693
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12693 ≤ (1.035819180631 : ℝ) := by
  have hr : (112.663214937263 : ℝ) ≤ √(12693 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.663214937263 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12693 12693 (11 / 1000) ≤
    (0.008484464354 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12693) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.663214937263 : ℝ) ≤ √(12693 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12693)
  have hdiv : K / √(12693 : ℝ) ≤ K / 112.663214937263 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.663214937263 ≤ (0.008484464354 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12693.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12693 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12693 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12693 := gPlus_lower 12693
end BstLean.Part269.N12693

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12693
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035819180630 : ℝ) ≤ wn 12693 := by
  have hn : √(12693 : ℝ) ≤ 112.663214937264 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12693 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.663214937264 ≤ 2 / √(12693 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000252022201 : ℝ) ≤ rhoBar 12693 BstLean.Part154.csC ∧
    rhoBar 12693 BstLean.Part154.csC ≤ 0.000252022591 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035819180630 : ℝ) / (1.295212 * 12693) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035819180631 : ℝ) / (1.29521 * 12693) := by gcongr
      _ ≤ (0.000252022591 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12693 BstLean.Part154.csC) ≤ 0.001008153880 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12693 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12693 BstLean.Part154.csC) (piBar (rhoBar 12693 BstLean.Part154.csC)) ≤ 0.000192496560 ∧
    cc1 (rhoBar 12693 BstLean.Part154.csC) (piBar (rhoBar 12693 BstLean.Part154.csC)) ≤ 0.000122486838 ∧
    cc2 (rhoBar 12693 BstLean.Part154.csC) ≤ 0.000071104547 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12693 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12693 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12693 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12693 BstLean.Part154.csC * nuR (rhoBar 12693 BstLean.Part154.csC)) ≤ 0.000504061061 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000252022591 : ℝ) * 0.001008153880 := by gcongr
      _ ≤ (0.000504061061 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12693 BstLean.Part154.csC) * nuR (rhoBar 12693 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001008153880 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12693 BstLean.Part154.csC) * rhoBar 12693 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000252022591 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000252022591 / 2 + 0.399 * 0.001008153880 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000192496560 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000504061061 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122486838 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000252022591 / 1.414213562 := by gcongr
      _ ≤ (0.000071104547 : ℝ) := by norm_num

end BstLean.Part269.N12693

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12693
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12693 BstLean.Part154.csC) (piBar (rhoBar 12693 BstLean.Part154.csC)) ≤ 1.60023E-7 := by
  have hr0 : 0 ≤ rhoBar 12693 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12693 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12693 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12693 BstLean.Part154.csC) (piBar (rhoBar 12693 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12693 BstLean.Part154.csC) (piBar (rhoBar 12693 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12693 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000192496560 : ℝ) ^ 2 + 0.000122486838 ^ 2 + 3 * 0.000071104547 ^ 2 +
        2 * 0.797885 * 0.000192496560 * 0.000122486838 + 2 * 0.000192496560 * 0.000071104547 +
        4 * 0.797885 * 0.000122486838 * 0.000071104547 := by gcongr
    _ ≤ (1.60023E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12693 BstLean.Part154.csC Θ ≤ 0.002630798273 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12693 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12693 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12693 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12693 BstLean.Part154.csC) (piBar (rhoBar 12693 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12693 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035819180631 * 1.60023E-7 / (0.000252022201 : ℝ) := by gcongr
    _ ≤ 0.002630798273 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12693 BstLean.Part154.csC Θ ≤ 0.002919031185 + 0.000664758082 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12693 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12693 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12693 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035819180631 : ℝ) * ((2 * Θ * 0.000252022591 +
        (6863 / 10000) * 0.000252022591 * 12693 * 0.001008153880) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002919031185 + 0.000664758082 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12693 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12693 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12693 0.011 Θ ∧ gammaRatio 12693 0.011 Θ ≤ 0.000086638850 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12693 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035819180631 : ℝ) * 0.525 / ((1 - 0.011) * 12693) := by gcongr
      _ ≤ (0.000086638850 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12693 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12693 0.011 Θ) :=
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
    badAllowance 12693 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000615501984 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12693 BstLean.Part154.csC) 1.22 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 2 (rhoBar 12693 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12693 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12693 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12693 0.011 Θ) 1.12 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 1 (gammaRatio 12693 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12693 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12693 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12693 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12693 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035819180631 : ℝ) * 12693 *
        (2.2721E-8 / 1.1045361 + 2.7751E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000615501984 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12693 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003534533169 + 0.003295556355 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12693

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12693
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12693 BstLean.Part154.csC) (piBar (rhoBar 12693 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12693 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12693 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12693 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12693 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12693 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12693 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12693 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12693 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12693 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12693 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12693 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12693 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12693 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12693 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052498939911 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12693) ≤ 0.010600066595 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12693 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035819180631)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010600066595 + 2 * 0.737676 / 12693) := by gcongr
    _ ≤ (0.052498939911 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12693 12 ≤ 0.0015 := by
  exact BstLean.Part269.S13.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12693

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12693
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560503251555 : ℝ) ≤ plow 12693 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12693) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052771300256)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001381169094) : eMP 12693 0.011 xi bn ≤ 0.001189046121 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12693 : ℝ) * (1 - 0.011))) ≤ 0.000587919819 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001381169094 / (12693 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000587919819 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000587919819 : ℝ) + 3.141593 * 0.052771300256 / (12693 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001189046121 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052771300256)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001381169094) : PiBarMP 12693 12 0.011 xi bn ≤ 0.161295990466 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12693 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037164083388 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.041853786877 : ℝ) ≤ √((12693 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.663214937263 : ℝ) ≤ √(12693 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12693) ≤ 0.123664217026 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037164083388 + 0.052771300256 * 1.772454 / (2 * (112.041853786877 : ℝ))) * (1 + 0.001189046121) +
        8 / (12693 * 112.663214937263) + 0.123664217026 := by gcongr
    _ ≤ (0.161295990466 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052771300256)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001381169094) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282218987482) :
    parallelOracle 12693 0.011 xi bn cd ≤ 0.162287060280 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12693 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12693 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560503251555 : ℝ) ≤ plow 12693 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.663214937263 : ℝ) ≤ √(12693 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282218987482 : ℝ) / (2 * 0.560503251555 * 112.663214937263)) * 0.161295990466 +
        0.282218987482 ^ 2 / (2 * 0.560503251555 * 112.663214937263) := by gcongr
    _ ≤ (0.162287060280 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052771300256) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001381169094)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282218987482) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12693 12693 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560503251555 : ℝ) ≤ plow 12693 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.663214937263 : ℝ) ≤ √(12693 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12693 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12693 Θ 1.22 ≤ 0.011770483390 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.663214937263 := by gcongr <;> linarith
      _ ≤ (0.011770483390 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12693 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12693 12693 0.011 ≤ 0.008484464354 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12693 12693 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12693 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12693 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12693 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12693 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162287060280 + 0.011770483390 + (0.008484464354 : ℝ) *
        (1 + 2 * (0.282218987482 + 0.011770483390) / (0.560503251555 * 112.663214937263))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12693]

end BstLean.Part269.N12693

/-! The original eight local profiles supply actual 12693 moment certificates. -/
namespace BstLean.Part269.N12693
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12693 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12693 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12693 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052771300256 ∧
    0 ≤ bN 12693 BstLean.Part154.csC (groupTheta g) ∧ bN 12693 BstLean.Part154.csC (groupTheta g) ≤ 0.001381169094 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12693 12693 0.011
      (momentAllowance 12693 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12693 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12693 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12693 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12693 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12693 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229720047571 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12693 0.011
      (momentAllowance 12693 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12693 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12693
/-! The actual computed-centre upper energy formula at 12693. -/
namespace BstLean.Part269.N12693
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12693

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12693
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12693)
open BstLean.Part268 (cell12693)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085510696893
  | 2 => 0.086453822301
  | 3 => 0.087395142308
  | 4 => 0.088336087631
  | 5 => 0.089278388383
  | 6 => 0.090224118486
  | 7 => 0.091175744257
  | 8 => 0.092136177199
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12693 12693 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12693 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003538895953 + 0.003300387184 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S13.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12693

/-! Actual upper energy certificates on all 43 source endpoints at 12693. -/
namespace BstLean.Part269.N12693
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12693)
open BstLean.Part268 (cell12693)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12693 (gMinus 12693) (1 - (cell12693 i).lower) ≤ 1 ∧
    energyUpper 12693 (gMinus 12693) (BstLean.Part211.gPlus 12693)
      (finiteEnergy 12693 12693 0.011) (1 - (cell12693 i).lower) ≤
      (cell12693 i).energy := by
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
      have E := BstLean.Part269.S13.uniformEnergy10 (n := 12693) (by norm_num)
        (q := 1 - (cell12693 ⟨10,by decide⟩).lower)
        (by norm_num [cell12693]) (by norm_num [cell12693])
      exact ⟨E.1,E.2.trans (by norm_num [cell12693])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy11 (n := 12693) (by norm_num)
        (q := 1 - (cell12693 ⟨11,by decide⟩).lower)
        (by norm_num [cell12693]) (by norm_num [cell12693])
      exact ⟨E.1,E.2.trans (by norm_num [cell12693])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy12 (n := 12693) (by norm_num)
        (q := 1 - (cell12693 ⟨12,by decide⟩).lower)
        (by norm_num [cell12693]) (by norm_num [cell12693])
      exact ⟨E.1,E.2.trans (by norm_num [cell12693])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy13 (n := 12693) (by norm_num)
        (q := 1 - (cell12693 ⟨13,by decide⟩).lower)
        (by norm_num [cell12693]) (by norm_num [cell12693])
      exact ⟨E.1,E.2.trans (by norm_num [cell12693])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy14 (n := 12693) (by norm_num)
        (q := 1 - (cell12693 ⟨14,by decide⟩).lower)
        (by norm_num [cell12693]) (by norm_num [cell12693])
      exact ⟨E.1,E.2.trans (by norm_num [cell12693])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy15 (n := 12693) (by norm_num)
        (q := 1 - (cell12693 ⟨15,by decide⟩).lower)
        (by norm_num [cell12693]) (by norm_num [cell12693])
      exact ⟨E.1,E.2.trans (by norm_num [cell12693])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy16 (n := 12693) (by norm_num)
        (q := 1 - (cell12693 ⟨16,by decide⟩).lower)
        (by norm_num [cell12693]) (by norm_num [cell12693])
      exact ⟨E.1,E.2.trans (by norm_num [cell12693])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy17 (n := 12693) (by norm_num)
        (q := 1 - (cell12693 ⟨17,by decide⟩).lower)
        (by norm_num [cell12693]) (by norm_num [cell12693])
      exact ⟨E.1,E.2.trans (by norm_num [cell12693])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy18 (n := 12693) (by norm_num)
        (q := 1 - (cell12693 ⟨18,by decide⟩).lower)
        (by norm_num [cell12693]) (by norm_num [cell12693])
      exact ⟨E.1,E.2.trans (by norm_num [cell12693])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy19 (n := 12693) (by norm_num)
        (q := 1 - (cell12693 ⟨19,by decide⟩).lower)
        (by norm_num [cell12693]) (by norm_num [cell12693])
      exact ⟨E.1,E.2.trans (by norm_num [cell12693])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy20 (n := 12693) (by norm_num)
        (q := 1 - (cell12693 ⟨20,by decide⟩).lower)
        (by norm_num [cell12693]) (by norm_num [cell12693])
      exact ⟨E.1,E.2.trans (by norm_num [cell12693])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy21 (n := 12693) (by norm_num)
        (q := 1 - (cell12693 ⟨21,by decide⟩).lower)
        (by norm_num [cell12693]) (by norm_num [cell12693])
      exact ⟨E.1,E.2.trans (by norm_num [cell12693])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy22 (n := 12693) (by norm_num)
        (q := 1 - (cell12693 ⟨22,by decide⟩).lower)
        (by norm_num [cell12693]) (by norm_num [cell12693])
      exact ⟨E.1,E.2.trans (by norm_num [cell12693])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy23 (n := 12693) (by norm_num)
        (q := 1 - (cell12693 ⟨23,by decide⟩).lower)
        (by norm_num [cell12693]) (by norm_num [cell12693])
      exact ⟨E.1,E.2.trans (by norm_num [cell12693])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy24 (n := 12693) (by norm_num)
        (q := 1 - (cell12693 ⟨24,by decide⟩).lower)
        (by norm_num [cell12693]) (by norm_num [cell12693])
      exact ⟨E.1,E.2.trans (by norm_num [cell12693])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy25 (n := 12693) (by norm_num)
        (q := 1 - (cell12693 ⟨25,by decide⟩).lower)
        (by norm_num [cell12693]) (by norm_num [cell12693])
      exact ⟨E.1,E.2.trans (by norm_num [cell12693])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy26 (n := 12693) (by norm_num)
        (q := 1 - (cell12693 ⟨26,by decide⟩).lower)
        (by norm_num [cell12693]) (by norm_num [cell12693])
      exact ⟨E.1,E.2.trans (by norm_num [cell12693])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy27 (n := 12693) (by norm_num)
        (q := 1 - (cell12693 ⟨27,by decide⟩).lower)
        (by norm_num [cell12693]) (by norm_num [cell12693])
      exact ⟨E.1,E.2.trans (by norm_num [cell12693])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy28 (n := 12693) (by norm_num)
        (q := 1 - (cell12693 ⟨28,by decide⟩).lower)
        (by norm_num [cell12693]) (by norm_num [cell12693])
      exact ⟨E.1,E.2.trans (by norm_num [cell12693])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy29 (n := 12693) (by norm_num)
        (q := 1 - (cell12693 ⟨29,by decide⟩).lower)
        (by norm_num [cell12693]) (by norm_num [cell12693])
      exact ⟨E.1,E.2.trans (by norm_num [cell12693])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy30 (n := 12693) (by norm_num)
        (q := 1 - (cell12693 ⟨30,by decide⟩).lower)
        (by norm_num [cell12693]) (by norm_num [cell12693])
      exact ⟨E.1,E.2.trans (by norm_num [cell12693])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy31 (n := 12693) (by norm_num)
        (q := 1 - (cell12693 ⟨31,by decide⟩).lower)
        (by norm_num [cell12693]) (by norm_num [cell12693])
      exact ⟨E.1,E.2.trans (by norm_num [cell12693])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy32 (n := 12693) (by norm_num)
        (q := 1 - (cell12693 ⟨32,by decide⟩).lower)
        (by norm_num [cell12693]) (by norm_num [cell12693])
      exact ⟨E.1,E.2.trans (by norm_num [cell12693])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy33 (n := 12693) (by norm_num)
        (q := 1 - (cell12693 ⟨33,by decide⟩).lower)
        (by norm_num [cell12693]) (by norm_num [cell12693])
      exact ⟨E.1,E.2.trans (by norm_num [cell12693])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy34 (n := 12693) (by norm_num)
        (q := 1 - (cell12693 ⟨34,by decide⟩).lower)
        (by norm_num [cell12693]) (by norm_num [cell12693])
      exact ⟨E.1,E.2.trans (by norm_num [cell12693])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy35 (n := 12693) (by norm_num)
        (q := 1 - (cell12693 ⟨35,by decide⟩).lower)
        (by norm_num [cell12693]) (by norm_num [cell12693])
      exact ⟨E.1,E.2.trans (by norm_num [cell12693])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy36 (n := 12693) (by norm_num)
        (q := 1 - (cell12693 ⟨36,by decide⟩).lower)
        (by norm_num [cell12693]) (by norm_num [cell12693])
      exact ⟨E.1,E.2.trans (by norm_num [cell12693])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy37 (n := 12693) (by norm_num)
        (q := 1 - (cell12693 ⟨37,by decide⟩).lower)
        (by norm_num [cell12693]) (by norm_num [cell12693])
      exact ⟨E.1,E.2.trans (by norm_num [cell12693])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy38 (n := 12693) (by norm_num)
        (q := 1 - (cell12693 ⟨38,by decide⟩).lower)
        (by norm_num [cell12693]) (by norm_num [cell12693])
      exact ⟨E.1,E.2.trans (by norm_num [cell12693])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy39 (n := 12693) (by norm_num)
        (q := 1 - (cell12693 ⟨39,by decide⟩).lower)
        (by norm_num [cell12693]) (by norm_num [cell12693])
      exact ⟨E.1,E.2.trans (by norm_num [cell12693])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy40 (n := 12693) (by norm_num)
        (q := 1 - (cell12693 ⟨40,by decide⟩).lower)
        (by norm_num [cell12693]) (by norm_num [cell12693])
      exact ⟨E.1,E.2.trans (by norm_num [cell12693])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy41 (n := 12693) (by norm_num)
        (q := 1 - (cell12693 ⟨41,by decide⟩).lower)
        (by norm_num [cell12693]) (by norm_num [cell12693])
      exact ⟨E.1,E.2.trans (by norm_num [cell12693])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy42 (n := 12693) (by norm_num)
        (q := 1 - (cell12693 ⟨42,by decide⟩).lower)
        (by norm_num [cell12693]) (by norm_num [cell12693])
      exact ⟨E.1,E.2.trans (by norm_num [cell12693])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy43 (n := 12693) (by norm_num)
        (q := 1 - (cell12693 ⟨43,by decide⟩).lower)
        (by norm_num [cell12693]) (by norm_num [cell12693])
      exact ⟨E.1,E.2.trans (by norm_num [cell12693])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy44 (n := 12693) (by norm_num)
        (q := 1 - (cell12693 ⟨44,by decide⟩).lower)
        (by norm_num [cell12693]) (by norm_num [cell12693])
      exact ⟨E.1,E.2.trans (by norm_num [cell12693])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy45 (n := 12693) (by norm_num)
        (q := 1 - (cell12693 ⟨45,by decide⟩).lower)
        (by norm_num [cell12693]) (by norm_num [cell12693])
      exact ⟨E.1,E.2.trans (by norm_num [cell12693])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy46 (n := 12693) (by norm_num)
        (q := 1 - (cell12693 ⟨46,by decide⟩).lower)
        (by norm_num [cell12693]) (by norm_num [cell12693])
      exact ⟨E.1,E.2.trans (by norm_num [cell12693])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy47 (n := 12693) (by norm_num)
        (q := 1 - (cell12693 ⟨47,by decide⟩).lower)
        (by norm_num [cell12693]) (by norm_num [cell12693])
      exact ⟨E.1,E.2.trans (by norm_num [cell12693])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy48 (n := 12693) (by norm_num)
        (q := 1 - (cell12693 ⟨48,by decide⟩).lower)
        (by norm_num [cell12693]) (by norm_num [cell12693])
      exact ⟨E.1,E.2.trans (by norm_num [cell12693])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy49 (n := 12693) (by norm_num)
        (q := 1 - (cell12693 ⟨49,by decide⟩).lower)
        (by norm_num [cell12693]) (by norm_num [cell12693])
      exact ⟨E.1,E.2.trans (by norm_num [cell12693])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy50 (n := 12693) (by norm_num)
        (q := 1 - (cell12693 ⟨50,by decide⟩).lower)
        (by norm_num [cell12693]) (by norm_num [cell12693])
      exact ⟨E.1,E.2.trans (by norm_num [cell12693])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy51 (n := 12693) (by norm_num)
        (q := 1 - (cell12693 ⟨51,by decide⟩).lower)
        (by norm_num [cell12693]) (by norm_num [cell12693])
      exact ⟨E.1,E.2.trans (by norm_num [cell12693])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy52 (n := 12693) (by norm_num)
        (q := 1 - (cell12693 ⟨52,by decide⟩).lower)
        (by norm_num [cell12693]) (by norm_num [cell12693])
      exact ⟨E.1,E.2.trans (by norm_num [cell12693])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12693

/-! Source-cell containment and simple scalar guards at 12693. -/
namespace BstLean.Part269.N12693
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12693)
open BstLean.Part268 (cell12693)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12693 ⟨10,by decide⟩).lower ∧ (cell12693 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12693 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12693 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12693 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12693 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12693 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12693,cell12693,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12693 ⟨11,by decide⟩).lower ∧ (cell12693 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12693 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12693 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12693 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12693 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12693 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12693,cell12693,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12693 ⟨12,by decide⟩).lower ∧ (cell12693 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12693 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12693 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12693 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12693 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12693 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12693,cell12693,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12693 ⟨13,by decide⟩).lower ∧ (cell12693 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12693 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12693 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12693 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12693 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12693 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12693,cell12693,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12693 ⟨14,by decide⟩).lower ∧ (cell12693 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12693 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12693 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12693 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12693 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12693 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12693,cell12693,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12693 ⟨15,by decide⟩).lower ∧ (cell12693 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12693 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12693 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12693 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12693 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12693 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12693,cell12693,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12693 ⟨16,by decide⟩).lower ∧ (cell12693 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12693 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12693 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12693 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12693 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12693 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12693,cell12693,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12693 ⟨17,by decide⟩).lower ∧ (cell12693 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12693 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12693 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12693 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12693 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12693 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12693,cell12693,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12693 ⟨18,by decide⟩).lower ∧ (cell12693 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12693 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12693 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12693 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12693 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12693 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12693,cell12693,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12693 ⟨19,by decide⟩).lower ∧ (cell12693 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12693 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12693 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12693 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12693 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12693 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12693,cell12693,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12693 ⟨20,by decide⟩).lower ∧ (cell12693 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12693 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12693 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12693 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12693 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12693 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12693,cell12693,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12693 ⟨21,by decide⟩).lower ∧ (cell12693 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12693 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12693 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12693 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12693 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12693 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12693,cell12693,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12693 ⟨22,by decide⟩).lower ∧ (cell12693 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12693 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12693 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12693 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12693 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12693 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12693,cell12693,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12693 ⟨23,by decide⟩).lower ∧ (cell12693 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12693 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12693 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12693 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12693 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12693 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12693,cell12693,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12693 ⟨24,by decide⟩).lower ∧ (cell12693 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12693 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12693 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12693 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12693 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12693 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12693,cell12693,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12693 ⟨25,by decide⟩).lower ∧ (cell12693 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12693 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12693 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12693 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12693 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12693 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12693,cell12693,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12693 ⟨26,by decide⟩).lower ∧ (cell12693 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12693 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12693 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12693 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12693 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12693 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12693,cell12693,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12693 ⟨27,by decide⟩).lower ∧ (cell12693 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12693 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12693 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12693 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12693 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12693 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12693,cell12693,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12693 ⟨28,by decide⟩).lower ∧ (cell12693 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12693 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12693 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12693 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12693 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12693 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12693,cell12693,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12693 ⟨29,by decide⟩).lower ∧ (cell12693 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12693 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12693 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12693 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12693 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12693 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12693,cell12693,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12693 ⟨30,by decide⟩).lower ∧ (cell12693 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12693 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12693 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12693 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12693 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12693 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12693,cell12693,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12693 ⟨31,by decide⟩).lower ∧ (cell12693 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12693 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12693 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12693 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12693 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12693 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12693,cell12693,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12693 ⟨32,by decide⟩).lower ∧ (cell12693 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12693 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12693 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12693 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12693 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12693 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12693,cell12693,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12693 ⟨33,by decide⟩).lower ∧ (cell12693 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12693 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12693 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12693 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12693 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12693 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12693,cell12693,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12693 ⟨34,by decide⟩).lower ∧ (cell12693 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12693 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12693 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12693 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12693 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12693 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12693,cell12693,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12693 ⟨35,by decide⟩).lower ∧ (cell12693 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12693 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12693 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12693 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12693 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12693 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12693,cell12693,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12693 ⟨36,by decide⟩).lower ∧ (cell12693 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12693 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12693 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12693 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12693 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12693 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12693,cell12693,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12693 ⟨37,by decide⟩).lower ∧ (cell12693 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12693 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12693 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12693 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12693 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12693 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12693,cell12693,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12693 ⟨38,by decide⟩).lower ∧ (cell12693 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12693 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12693 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12693 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12693 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12693 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12693,cell12693,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12693 ⟨39,by decide⟩).lower ∧ (cell12693 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12693 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12693 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12693 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12693 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12693 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12693,cell12693,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12693 ⟨40,by decide⟩).lower ∧ (cell12693 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12693 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12693 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12693 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12693 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12693 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12693,cell12693,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12693 ⟨41,by decide⟩).lower ∧ (cell12693 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12693 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12693 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12693 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12693 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12693 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12693,cell12693,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12693 ⟨42,by decide⟩).lower ∧ (cell12693 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12693 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12693 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12693 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12693 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12693 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12693,cell12693,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12693 ⟨43,by decide⟩).lower ∧ (cell12693 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12693 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12693 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12693 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12693 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12693 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12693,cell12693,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12693 ⟨44,by decide⟩).lower ∧ (cell12693 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12693 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12693 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12693 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12693 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12693 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12693,cell12693,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12693 ⟨45,by decide⟩).lower ∧ (cell12693 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12693 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12693 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12693 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12693 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12693 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12693,cell12693,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12693 ⟨46,by decide⟩).lower ∧ (cell12693 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12693 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12693 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12693 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12693 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12693 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12693,cell12693,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12693 ⟨47,by decide⟩).lower ∧ (cell12693 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12693 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12693 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12693 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12693 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12693 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12693,cell12693,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12693 ⟨48,by decide⟩).lower ∧ (cell12693 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12693 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12693 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12693 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12693 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12693 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12693,cell12693,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12693 ⟨49,by decide⟩).lower ∧ (cell12693 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12693 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12693 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12693 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12693 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12693 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12693,cell12693,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12693 ⟨50,by decide⟩).lower ∧ (cell12693 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12693 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12693 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12693 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12693 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12693 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12693,cell12693,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12693 ⟨51,by decide⟩).lower ∧ (cell12693 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12693 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12693 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12693 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12693 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12693 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12693,cell12693,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12693 ⟨52,by decide⟩).lower ∧ (cell12693 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12693 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12693 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12693 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12693 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12693 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12693,cell12693,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12693 i).lower ∧
    (cell12693 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12693 i).upper ≤ (0.532 : ℝ) ∧
    (cell12693 i).centre ≤ (0.1 : ℝ) ∧ (cell12693 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12693 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12693 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12693

/-! The local source numeric instances at 12693 have no network premises. -/
namespace BstLean.Part269.N12693
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12693)
open BstLean.Part268 (cell12693)

noncomputable def sourceNumerics12693 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12693 (cell12693 i)
      scalarRow12693.M scalarRow12693.H scalarRow12693.xi := by
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
    energy_allowance := scalarRow12693.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12693]
    centre_nonneg := (scalarRow12693.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D13.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12693])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12693
/-! Actual 12694 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12694
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12694 ≤ (1.035817757321 : ℝ) := by
  have hr : (112.667652855644 : ℝ) ≤ √(12694 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.667652855644 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12694 12694 (11 / 1000) ≤
    (0.008484130153 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12694) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.667652855644 : ℝ) ≤ √(12694 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12694)
  have hdiv : K / √(12694 : ℝ) ≤ K / 112.667652855644 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.667652855644 ≤ (0.008484130153 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12694.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12694 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12694 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12694 := gPlus_lower 12694
end BstLean.Part269.N12694

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12694
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035817757320 : ℝ) ≤ wn 12694 := by
  have hn : √(12694 : ℝ) ≤ 112.667652855645 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12694 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.667652855645 ≤ 2 / √(12694 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000252002001 : ℝ) ≤ rhoBar 12694 BstLean.Part154.csC ∧
    rhoBar 12694 BstLean.Part154.csC ≤ 0.000252002391 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035817757320 : ℝ) / (1.295212 * 12694) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035817757321 : ℝ) / (1.29521 * 12694) := by gcongr
      _ ≤ (0.000252002391 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12694 BstLean.Part154.csC) ≤ 0.001008073070 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12694 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12694 BstLean.Part154.csC) (piBar (rhoBar 12694 BstLean.Part154.csC)) ≤ 0.000192481131 ∧
    cc1 (rhoBar 12694 BstLean.Part154.csC) (piBar (rhoBar 12694 BstLean.Part154.csC)) ≤ 0.000122477021 ∧
    cc2 (rhoBar 12694 BstLean.Part154.csC) ≤ 0.000071098848 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12694 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12694 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12694 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12694 BstLean.Part154.csC * nuR (rhoBar 12694 BstLean.Part154.csC)) ≤ 0.000504020659 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000252002391 : ℝ) * 0.001008073070 := by gcongr
      _ ≤ (0.000504020659 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12694 BstLean.Part154.csC) * nuR (rhoBar 12694 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001008073070 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12694 BstLean.Part154.csC) * rhoBar 12694 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000252002391 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000252002391 / 2 + 0.399 * 0.001008073070 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000192481131 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000504020659 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122477021 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000252002391 / 1.414213562 := by gcongr
      _ ≤ (0.000071098848 : ℝ) := by norm_num

end BstLean.Part269.N12694

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12694
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12694 BstLean.Part154.csC) (piBar (rhoBar 12694 BstLean.Part154.csC)) ≤ 1.59997E-7 := by
  have hr0 : 0 ≤ rhoBar 12694 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12694 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12694 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12694 BstLean.Part154.csC) (piBar (rhoBar 12694 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12694 BstLean.Part154.csC) (piBar (rhoBar 12694 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12694 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000192481131 : ℝ) ^ 2 + 0.000122477021 ^ 2 + 3 * 0.000071098848 ^ 2 +
        2 * 0.797885 * 0.000192481131 * 0.000122477021 + 2 * 0.000192481131 * 0.000071098848 +
        4 * 0.797885 * 0.000122477021 * 0.000071098848 := by gcongr
    _ ≤ (1.59997E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12694 BstLean.Part154.csC Θ ≤ 0.002630578060 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12694 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12694 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12694 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12694 BstLean.Part154.csC) (piBar (rhoBar 12694 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12694 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035817757321 * 1.59997E-7 / (0.000252002001 : ℝ) := by gcongr
    _ ≤ 0.002630578060 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12694 BstLean.Part154.csC Θ ≤ 0.002918789184 + 0.000664703887 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12694 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12694 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12694 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035817757321 : ℝ) * ((2 * Θ * 0.000252002391 +
        (6863 / 10000) * 0.000252002391 * 12694 * 0.001008073070) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002918789184 + 0.000664703887 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12694 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12694 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12694 0.011 Θ ∧ gammaRatio 12694 0.011 Θ ≤ 0.000086631906 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12694 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035817757321 : ℝ) * 0.525 / ((1 - 0.011) * 12694) := by gcongr
      _ ≤ (0.000086631906 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12694 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12694 0.011 Θ) :=
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
    badAllowance 12694 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000615501984 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12694 BstLean.Part154.csC) 1.22 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 2 (rhoBar 12694 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12694 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12694 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12694 0.011 Θ) 1.12 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 1 (gammaRatio 12694 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12694 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12694 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12694 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12694 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035817757321 : ℝ) * 12694 *
        (2.2721E-8 / 1.1045361 + 2.7751E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000615501984 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12694 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003534291168 + 0.003295281947 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12694

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12694
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12694 BstLean.Part154.csC) (piBar (rhoBar 12694 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12694 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12694 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12694 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12694 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12694 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12694 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12694 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12694 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12694 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12694 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12694 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12694 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12694 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12694 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052496849577 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12694) ≤ 0.010599649064 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12694 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035817757321)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010599649064 + 2 * 0.737676 / 12694) := by gcongr
    _ ≤ (0.052496849577 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12694 12 ≤ 0.0015 := by
  exact BstLean.Part269.S13.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12694

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12694
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560503296825 : ℝ) ≤ plow 12694 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12694) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052770914191)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001381053482) : eMP 12694 0.011 xi bn ≤ 0.001188949456 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12694 : ℝ) * (1 - 0.011))) ≤ 0.000587872055 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001381053482 / (12694 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000587872055 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000587872055 : ℝ) + 3.141593 * 0.052770914191 / (12694 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001188949456 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052770914191)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001381053482) : PiBarMP 12694 12 0.011 xi bn ≤ 0.161289538279 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12694 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037162527929 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.046267229212 : ℝ) ≤ √((12694 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.667652855644 : ℝ) ≤ √(12694 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12694) ≤ 0.123659345959 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037162527929 + 0.052770914191 * 1.772454 / (2 * (112.046267229212 : ℝ))) * (1 + 0.001188949456) +
        8 / (12694 * 112.667652855644) + 0.123659345959 := by gcongr
    _ ≤ (0.161289538279 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052770914191)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001381053482) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282216056852) :
    parallelOracle 12694 0.011 xi bn cd ≤ 0.162280537718 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12694 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12694 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560503296825 : ℝ) ≤ plow 12694 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.667652855644 : ℝ) ≤ √(12694 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282216056852 : ℝ) / (2 * 0.560503296825 * 112.667652855644)) * 0.161289538279 +
        0.282216056852 ^ 2 / (2 * 0.560503296825 * 112.667652855644) := by gcongr
    _ ≤ (0.162280537718 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052770914191) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001381053482)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282216056852) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12694 12694 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560503296825 : ℝ) ≤ plow 12694 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.667652855644 : ℝ) ≤ √(12694 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12694 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12694 Θ 1.22 ≤ 0.011770019757 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.667652855644 := by gcongr <;> linarith
      _ ≤ (0.011770019757 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12694 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12694 12694 0.011 ≤ 0.008484130153 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12694 12694 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12694 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12694 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12694 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12694 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162280537718 + 0.011770019757 + (0.008484130153 : ℝ) *
        (1 + 2 * (0.282216056852 + 0.011770019757) / (0.560503296825 * 112.667652855644))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12694]

end BstLean.Part269.N12694

/-! The original eight local profiles supply actual 12694 moment certificates. -/
namespace BstLean.Part269.N12694
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12694 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12694 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12694 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052770914191 ∧
    0 ≤ bN 12694 BstLean.Part154.csC (groupTheta g) ∧ bN 12694 BstLean.Part154.csC (groupTheta g) ≤ 0.001381053482 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12694 12694 0.011
      (momentAllowance 12694 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12694 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12694 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12694 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12694 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12694 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229719207275 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12694 0.011
      (momentAllowance 12694 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12694 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12694
/-! The actual computed-centre upper energy formula at 12694. -/
namespace BstLean.Part269.N12694
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12694

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12694
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12694)
open BstLean.Part268 (cell12694)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085507773529
  | 2 => 0.086450845068
  | 3 => 0.087392103322
  | 4 => 0.088332977193
  | 5 => 0.089275194660
  | 6 => 0.090220827149
  | 7 => 0.091172338083
  | 8 => 0.092132635623
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12694 12694 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12694 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003538895953 + 0.003300387184 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S13.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12694

/-! Actual upper energy certificates on all 43 source endpoints at 12694. -/
namespace BstLean.Part269.N12694
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12694)
open BstLean.Part268 (cell12694)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12694 (gMinus 12694) (1 - (cell12694 i).lower) ≤ 1 ∧
    energyUpper 12694 (gMinus 12694) (BstLean.Part211.gPlus 12694)
      (finiteEnergy 12694 12694 0.011) (1 - (cell12694 i).lower) ≤
      (cell12694 i).energy := by
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
      have E := BstLean.Part269.S13.uniformEnergy10 (n := 12694) (by norm_num)
        (q := 1 - (cell12694 ⟨10,by decide⟩).lower)
        (by norm_num [cell12694]) (by norm_num [cell12694])
      exact ⟨E.1,E.2.trans (by norm_num [cell12694])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy11 (n := 12694) (by norm_num)
        (q := 1 - (cell12694 ⟨11,by decide⟩).lower)
        (by norm_num [cell12694]) (by norm_num [cell12694])
      exact ⟨E.1,E.2.trans (by norm_num [cell12694])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy12 (n := 12694) (by norm_num)
        (q := 1 - (cell12694 ⟨12,by decide⟩).lower)
        (by norm_num [cell12694]) (by norm_num [cell12694])
      exact ⟨E.1,E.2.trans (by norm_num [cell12694])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy13 (n := 12694) (by norm_num)
        (q := 1 - (cell12694 ⟨13,by decide⟩).lower)
        (by norm_num [cell12694]) (by norm_num [cell12694])
      exact ⟨E.1,E.2.trans (by norm_num [cell12694])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy14 (n := 12694) (by norm_num)
        (q := 1 - (cell12694 ⟨14,by decide⟩).lower)
        (by norm_num [cell12694]) (by norm_num [cell12694])
      exact ⟨E.1,E.2.trans (by norm_num [cell12694])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy15 (n := 12694) (by norm_num)
        (q := 1 - (cell12694 ⟨15,by decide⟩).lower)
        (by norm_num [cell12694]) (by norm_num [cell12694])
      exact ⟨E.1,E.2.trans (by norm_num [cell12694])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy16 (n := 12694) (by norm_num)
        (q := 1 - (cell12694 ⟨16,by decide⟩).lower)
        (by norm_num [cell12694]) (by norm_num [cell12694])
      exact ⟨E.1,E.2.trans (by norm_num [cell12694])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy17 (n := 12694) (by norm_num)
        (q := 1 - (cell12694 ⟨17,by decide⟩).lower)
        (by norm_num [cell12694]) (by norm_num [cell12694])
      exact ⟨E.1,E.2.trans (by norm_num [cell12694])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy18 (n := 12694) (by norm_num)
        (q := 1 - (cell12694 ⟨18,by decide⟩).lower)
        (by norm_num [cell12694]) (by norm_num [cell12694])
      exact ⟨E.1,E.2.trans (by norm_num [cell12694])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy19 (n := 12694) (by norm_num)
        (q := 1 - (cell12694 ⟨19,by decide⟩).lower)
        (by norm_num [cell12694]) (by norm_num [cell12694])
      exact ⟨E.1,E.2.trans (by norm_num [cell12694])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy20 (n := 12694) (by norm_num)
        (q := 1 - (cell12694 ⟨20,by decide⟩).lower)
        (by norm_num [cell12694]) (by norm_num [cell12694])
      exact ⟨E.1,E.2.trans (by norm_num [cell12694])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy21 (n := 12694) (by norm_num)
        (q := 1 - (cell12694 ⟨21,by decide⟩).lower)
        (by norm_num [cell12694]) (by norm_num [cell12694])
      exact ⟨E.1,E.2.trans (by norm_num [cell12694])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy22 (n := 12694) (by norm_num)
        (q := 1 - (cell12694 ⟨22,by decide⟩).lower)
        (by norm_num [cell12694]) (by norm_num [cell12694])
      exact ⟨E.1,E.2.trans (by norm_num [cell12694])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy23 (n := 12694) (by norm_num)
        (q := 1 - (cell12694 ⟨23,by decide⟩).lower)
        (by norm_num [cell12694]) (by norm_num [cell12694])
      exact ⟨E.1,E.2.trans (by norm_num [cell12694])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy24 (n := 12694) (by norm_num)
        (q := 1 - (cell12694 ⟨24,by decide⟩).lower)
        (by norm_num [cell12694]) (by norm_num [cell12694])
      exact ⟨E.1,E.2.trans (by norm_num [cell12694])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy25 (n := 12694) (by norm_num)
        (q := 1 - (cell12694 ⟨25,by decide⟩).lower)
        (by norm_num [cell12694]) (by norm_num [cell12694])
      exact ⟨E.1,E.2.trans (by norm_num [cell12694])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy26 (n := 12694) (by norm_num)
        (q := 1 - (cell12694 ⟨26,by decide⟩).lower)
        (by norm_num [cell12694]) (by norm_num [cell12694])
      exact ⟨E.1,E.2.trans (by norm_num [cell12694])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy27 (n := 12694) (by norm_num)
        (q := 1 - (cell12694 ⟨27,by decide⟩).lower)
        (by norm_num [cell12694]) (by norm_num [cell12694])
      exact ⟨E.1,E.2.trans (by norm_num [cell12694])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy28 (n := 12694) (by norm_num)
        (q := 1 - (cell12694 ⟨28,by decide⟩).lower)
        (by norm_num [cell12694]) (by norm_num [cell12694])
      exact ⟨E.1,E.2.trans (by norm_num [cell12694])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy29 (n := 12694) (by norm_num)
        (q := 1 - (cell12694 ⟨29,by decide⟩).lower)
        (by norm_num [cell12694]) (by norm_num [cell12694])
      exact ⟨E.1,E.2.trans (by norm_num [cell12694])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy30 (n := 12694) (by norm_num)
        (q := 1 - (cell12694 ⟨30,by decide⟩).lower)
        (by norm_num [cell12694]) (by norm_num [cell12694])
      exact ⟨E.1,E.2.trans (by norm_num [cell12694])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy31 (n := 12694) (by norm_num)
        (q := 1 - (cell12694 ⟨31,by decide⟩).lower)
        (by norm_num [cell12694]) (by norm_num [cell12694])
      exact ⟨E.1,E.2.trans (by norm_num [cell12694])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy32 (n := 12694) (by norm_num)
        (q := 1 - (cell12694 ⟨32,by decide⟩).lower)
        (by norm_num [cell12694]) (by norm_num [cell12694])
      exact ⟨E.1,E.2.trans (by norm_num [cell12694])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy33 (n := 12694) (by norm_num)
        (q := 1 - (cell12694 ⟨33,by decide⟩).lower)
        (by norm_num [cell12694]) (by norm_num [cell12694])
      exact ⟨E.1,E.2.trans (by norm_num [cell12694])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy34 (n := 12694) (by norm_num)
        (q := 1 - (cell12694 ⟨34,by decide⟩).lower)
        (by norm_num [cell12694]) (by norm_num [cell12694])
      exact ⟨E.1,E.2.trans (by norm_num [cell12694])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy35 (n := 12694) (by norm_num)
        (q := 1 - (cell12694 ⟨35,by decide⟩).lower)
        (by norm_num [cell12694]) (by norm_num [cell12694])
      exact ⟨E.1,E.2.trans (by norm_num [cell12694])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy36 (n := 12694) (by norm_num)
        (q := 1 - (cell12694 ⟨36,by decide⟩).lower)
        (by norm_num [cell12694]) (by norm_num [cell12694])
      exact ⟨E.1,E.2.trans (by norm_num [cell12694])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy37 (n := 12694) (by norm_num)
        (q := 1 - (cell12694 ⟨37,by decide⟩).lower)
        (by norm_num [cell12694]) (by norm_num [cell12694])
      exact ⟨E.1,E.2.trans (by norm_num [cell12694])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy38 (n := 12694) (by norm_num)
        (q := 1 - (cell12694 ⟨38,by decide⟩).lower)
        (by norm_num [cell12694]) (by norm_num [cell12694])
      exact ⟨E.1,E.2.trans (by norm_num [cell12694])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy39 (n := 12694) (by norm_num)
        (q := 1 - (cell12694 ⟨39,by decide⟩).lower)
        (by norm_num [cell12694]) (by norm_num [cell12694])
      exact ⟨E.1,E.2.trans (by norm_num [cell12694])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy40 (n := 12694) (by norm_num)
        (q := 1 - (cell12694 ⟨40,by decide⟩).lower)
        (by norm_num [cell12694]) (by norm_num [cell12694])
      exact ⟨E.1,E.2.trans (by norm_num [cell12694])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy41 (n := 12694) (by norm_num)
        (q := 1 - (cell12694 ⟨41,by decide⟩).lower)
        (by norm_num [cell12694]) (by norm_num [cell12694])
      exact ⟨E.1,E.2.trans (by norm_num [cell12694])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy42 (n := 12694) (by norm_num)
        (q := 1 - (cell12694 ⟨42,by decide⟩).lower)
        (by norm_num [cell12694]) (by norm_num [cell12694])
      exact ⟨E.1,E.2.trans (by norm_num [cell12694])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy43 (n := 12694) (by norm_num)
        (q := 1 - (cell12694 ⟨43,by decide⟩).lower)
        (by norm_num [cell12694]) (by norm_num [cell12694])
      exact ⟨E.1,E.2.trans (by norm_num [cell12694])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy44 (n := 12694) (by norm_num)
        (q := 1 - (cell12694 ⟨44,by decide⟩).lower)
        (by norm_num [cell12694]) (by norm_num [cell12694])
      exact ⟨E.1,E.2.trans (by norm_num [cell12694])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy45 (n := 12694) (by norm_num)
        (q := 1 - (cell12694 ⟨45,by decide⟩).lower)
        (by norm_num [cell12694]) (by norm_num [cell12694])
      exact ⟨E.1,E.2.trans (by norm_num [cell12694])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy46 (n := 12694) (by norm_num)
        (q := 1 - (cell12694 ⟨46,by decide⟩).lower)
        (by norm_num [cell12694]) (by norm_num [cell12694])
      exact ⟨E.1,E.2.trans (by norm_num [cell12694])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy47 (n := 12694) (by norm_num)
        (q := 1 - (cell12694 ⟨47,by decide⟩).lower)
        (by norm_num [cell12694]) (by norm_num [cell12694])
      exact ⟨E.1,E.2.trans (by norm_num [cell12694])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy48 (n := 12694) (by norm_num)
        (q := 1 - (cell12694 ⟨48,by decide⟩).lower)
        (by norm_num [cell12694]) (by norm_num [cell12694])
      exact ⟨E.1,E.2.trans (by norm_num [cell12694])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy49 (n := 12694) (by norm_num)
        (q := 1 - (cell12694 ⟨49,by decide⟩).lower)
        (by norm_num [cell12694]) (by norm_num [cell12694])
      exact ⟨E.1,E.2.trans (by norm_num [cell12694])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy50 (n := 12694) (by norm_num)
        (q := 1 - (cell12694 ⟨50,by decide⟩).lower)
        (by norm_num [cell12694]) (by norm_num [cell12694])
      exact ⟨E.1,E.2.trans (by norm_num [cell12694])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy51 (n := 12694) (by norm_num)
        (q := 1 - (cell12694 ⟨51,by decide⟩).lower)
        (by norm_num [cell12694]) (by norm_num [cell12694])
      exact ⟨E.1,E.2.trans (by norm_num [cell12694])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy52 (n := 12694) (by norm_num)
        (q := 1 - (cell12694 ⟨52,by decide⟩).lower)
        (by norm_num [cell12694]) (by norm_num [cell12694])
      exact ⟨E.1,E.2.trans (by norm_num [cell12694])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12694

/-! Source-cell containment and simple scalar guards at 12694. -/
namespace BstLean.Part269.N12694
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12694)
open BstLean.Part268 (cell12694)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12694 ⟨10,by decide⟩).lower ∧ (cell12694 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12694 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12694 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12694 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12694 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12694 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12694,cell12694,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12694 ⟨11,by decide⟩).lower ∧ (cell12694 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12694 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12694 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12694 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12694 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12694 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12694,cell12694,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12694 ⟨12,by decide⟩).lower ∧ (cell12694 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12694 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12694 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12694 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12694 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12694 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12694,cell12694,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12694 ⟨13,by decide⟩).lower ∧ (cell12694 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12694 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12694 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12694 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12694 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12694 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12694,cell12694,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12694 ⟨14,by decide⟩).lower ∧ (cell12694 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12694 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12694 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12694 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12694 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12694 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12694,cell12694,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12694 ⟨15,by decide⟩).lower ∧ (cell12694 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12694 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12694 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12694 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12694 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12694 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12694,cell12694,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12694 ⟨16,by decide⟩).lower ∧ (cell12694 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12694 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12694 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12694 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12694 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12694 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12694,cell12694,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12694 ⟨17,by decide⟩).lower ∧ (cell12694 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12694 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12694 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12694 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12694 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12694 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12694,cell12694,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12694 ⟨18,by decide⟩).lower ∧ (cell12694 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12694 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12694 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12694 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12694 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12694 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12694,cell12694,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12694 ⟨19,by decide⟩).lower ∧ (cell12694 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12694 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12694 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12694 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12694 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12694 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12694,cell12694,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12694 ⟨20,by decide⟩).lower ∧ (cell12694 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12694 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12694 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12694 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12694 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12694 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12694,cell12694,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12694 ⟨21,by decide⟩).lower ∧ (cell12694 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12694 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12694 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12694 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12694 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12694 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12694,cell12694,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12694 ⟨22,by decide⟩).lower ∧ (cell12694 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12694 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12694 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12694 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12694 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12694 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12694,cell12694,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12694 ⟨23,by decide⟩).lower ∧ (cell12694 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12694 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12694 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12694 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12694 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12694 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12694,cell12694,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12694 ⟨24,by decide⟩).lower ∧ (cell12694 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12694 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12694 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12694 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12694 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12694 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12694,cell12694,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12694 ⟨25,by decide⟩).lower ∧ (cell12694 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12694 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12694 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12694 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12694 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12694 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12694,cell12694,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12694 ⟨26,by decide⟩).lower ∧ (cell12694 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12694 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12694 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12694 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12694 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12694 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12694,cell12694,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12694 ⟨27,by decide⟩).lower ∧ (cell12694 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12694 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12694 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12694 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12694 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12694 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12694,cell12694,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12694 ⟨28,by decide⟩).lower ∧ (cell12694 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12694 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12694 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12694 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12694 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12694 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12694,cell12694,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12694 ⟨29,by decide⟩).lower ∧ (cell12694 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12694 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12694 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12694 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12694 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12694 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12694,cell12694,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12694 ⟨30,by decide⟩).lower ∧ (cell12694 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12694 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12694 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12694 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12694 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12694 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12694,cell12694,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12694 ⟨31,by decide⟩).lower ∧ (cell12694 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12694 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12694 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12694 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12694 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12694 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12694,cell12694,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12694 ⟨32,by decide⟩).lower ∧ (cell12694 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12694 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12694 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12694 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12694 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12694 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12694,cell12694,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12694 ⟨33,by decide⟩).lower ∧ (cell12694 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12694 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12694 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12694 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12694 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12694 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12694,cell12694,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12694 ⟨34,by decide⟩).lower ∧ (cell12694 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12694 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12694 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12694 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12694 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12694 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12694,cell12694,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12694 ⟨35,by decide⟩).lower ∧ (cell12694 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12694 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12694 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12694 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12694 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12694 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12694,cell12694,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12694 ⟨36,by decide⟩).lower ∧ (cell12694 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12694 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12694 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12694 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12694 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12694 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12694,cell12694,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12694 ⟨37,by decide⟩).lower ∧ (cell12694 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12694 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12694 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12694 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12694 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12694 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12694,cell12694,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12694 ⟨38,by decide⟩).lower ∧ (cell12694 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12694 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12694 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12694 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12694 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12694 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12694,cell12694,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12694 ⟨39,by decide⟩).lower ∧ (cell12694 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12694 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12694 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12694 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12694 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12694 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12694,cell12694,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12694 ⟨40,by decide⟩).lower ∧ (cell12694 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12694 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12694 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12694 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12694 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12694 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12694,cell12694,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12694 ⟨41,by decide⟩).lower ∧ (cell12694 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12694 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12694 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12694 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12694 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12694 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12694,cell12694,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12694 ⟨42,by decide⟩).lower ∧ (cell12694 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12694 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12694 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12694 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12694 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12694 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12694,cell12694,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12694 ⟨43,by decide⟩).lower ∧ (cell12694 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12694 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12694 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12694 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12694 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12694 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12694,cell12694,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12694 ⟨44,by decide⟩).lower ∧ (cell12694 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12694 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12694 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12694 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12694 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12694 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12694,cell12694,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12694 ⟨45,by decide⟩).lower ∧ (cell12694 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12694 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12694 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12694 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12694 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12694 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12694,cell12694,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12694 ⟨46,by decide⟩).lower ∧ (cell12694 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12694 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12694 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12694 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12694 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12694 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12694,cell12694,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12694 ⟨47,by decide⟩).lower ∧ (cell12694 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12694 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12694 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12694 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12694 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12694 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12694,cell12694,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12694 ⟨48,by decide⟩).lower ∧ (cell12694 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12694 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12694 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12694 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12694 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12694 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12694,cell12694,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12694 ⟨49,by decide⟩).lower ∧ (cell12694 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12694 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12694 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12694 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12694 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12694 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12694,cell12694,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12694 ⟨50,by decide⟩).lower ∧ (cell12694 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12694 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12694 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12694 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12694 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12694 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12694,cell12694,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12694 ⟨51,by decide⟩).lower ∧ (cell12694 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12694 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12694 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12694 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12694 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12694 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12694,cell12694,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12694 ⟨52,by decide⟩).lower ∧ (cell12694 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12694 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12694 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12694 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12694 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12694 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12694,cell12694,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12694 i).lower ∧
    (cell12694 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12694 i).upper ≤ (0.532 : ℝ) ∧
    (cell12694 i).centre ≤ (0.1 : ℝ) ∧ (cell12694 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12694 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12694 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12694

/-! The local source numeric instances at 12694 have no network premises. -/
namespace BstLean.Part269.N12694
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12694)
open BstLean.Part268 (cell12694)

noncomputable def sourceNumerics12694 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12694 (cell12694 i)
      scalarRow12694.M scalarRow12694.H scalarRow12694.xi := by
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
    energy_allowance := scalarRow12694.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12694]
    centre_nonneg := (scalarRow12694.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D13.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12694])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12694
/-! Actual 12695 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12695
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12695 ≤ (1.035816334179 : ℝ) := by
  have hr : (112.672090599225 : ℝ) ≤ √(12695 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.672090599225 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12695 12695 (11 / 1000) ≤
    (0.008483795991 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12695) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.672090599225 : ℝ) ≤ √(12695 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12695)
  have hdiv : K / √(12695 : ℝ) ≤ K / 112.672090599225 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.672090599225 ≤ (0.008483795991 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12695.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12695 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12695 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12695 := gPlus_lower 12695
end BstLean.Part269.N12695

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12695
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035816334178 : ℝ) ≤ wn 12695 := by
  have hn : √(12695 : ℝ) ≤ 112.672090599226 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12695 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.672090599226 ≤ 2 / √(12695 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000251981804 : ℝ) ≤ rhoBar 12695 BstLean.Part154.csC ∧
    rhoBar 12695 BstLean.Part154.csC ≤ 0.000251982194 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035816334178 : ℝ) / (1.295212 * 12695) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035816334179 : ℝ) / (1.29521 * 12695) := by gcongr
      _ ≤ (0.000251982194 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12695 BstLean.Part154.csC) ≤ 0.001007992272 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12695 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12695 BstLean.Part154.csC) (piBar (rhoBar 12695 BstLean.Part154.csC)) ≤ 0.000192465703 ∧
    cc1 (rhoBar 12695 BstLean.Part154.csC) (piBar (rhoBar 12695 BstLean.Part154.csC)) ≤ 0.000122467204 ∧
    cc2 (rhoBar 12695 BstLean.Part154.csC) ≤ 0.000071093149 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12695 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12695 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12695 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12695 BstLean.Part154.csC * nuR (rhoBar 12695 BstLean.Part154.csC)) ≤ 0.000503980262 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000251982194 : ℝ) * 0.001007992272 := by gcongr
      _ ≤ (0.000503980262 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12695 BstLean.Part154.csC) * nuR (rhoBar 12695 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001007992272 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12695 BstLean.Part154.csC) * rhoBar 12695 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000251982194 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000251982194 / 2 + 0.399 * 0.001007992272 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000192465703 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000503980262 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122467204 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000251982194 / 1.414213562 := by gcongr
      _ ≤ (0.000071093149 : ℝ) := by norm_num

end BstLean.Part269.N12695

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12695
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12695 BstLean.Part154.csC) (piBar (rhoBar 12695 BstLean.Part154.csC)) ≤ 1.59971E-7 := by
  have hr0 : 0 ≤ rhoBar 12695 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12695 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12695 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12695 BstLean.Part154.csC) (piBar (rhoBar 12695 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12695 BstLean.Part154.csC) (piBar (rhoBar 12695 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12695 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000192465703 : ℝ) ^ 2 + 0.000122467204 ^ 2 + 3 * 0.000071093149 ^ 2 +
        2 * 0.797885 * 0.000192465703 * 0.000122467204 + 2 * 0.000192465703 * 0.000071093149 +
        4 * 0.797885 * 0.000122467204 * 0.000071093149 := by gcongr
    _ ≤ (1.59971E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12695 BstLean.Part154.csC Θ ≤ 0.002630357783 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12695 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12695 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12695 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12695 BstLean.Part154.csC) (piBar (rhoBar 12695 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12695 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035816334179 * 1.59971E-7 / (0.000251981804 : ℝ) := by gcongr
    _ ≤ 0.002630357783 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12695 BstLean.Part154.csC Θ ≤ 0.002918547218 + 0.000664649700 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12695 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12695 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12695 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035816334179 : ℝ) * ((2 * Θ * 0.000251982194 +
        (6863 / 10000) * 0.000251982194 * 12695 * 0.001007992272) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002918547218 + 0.000664649700 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12695 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12695 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12695 0.011 Θ ∧ gammaRatio 12695 0.011 Θ ≤ 0.000086624963 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12695 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035816334179 : ℝ) * 0.525 / ((1 - 0.011) * 12695) := by gcongr
      _ ≤ (0.000086624963 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12695 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12695 0.011 Θ) :=
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
    badAllowance 12695 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000615501984 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12695 BstLean.Part154.csC) 1.22 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 2 (rhoBar 12695 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12695 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12695 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12695 0.011 Θ) 1.12 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 1 (gammaRatio 12695 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12695 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12695 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12695 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12695 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035816334179 : ℝ) * 12695 *
        (2.2721E-8 / 1.1045361 + 2.7751E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000615501984 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12695 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003534049202 + 0.003295007483 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12695

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12695
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12695 BstLean.Part154.csC) (piBar (rhoBar 12695 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12695 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12695 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12695 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12695 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12695 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12695 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12695 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12695 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12695 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12695 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12695 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12695 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12695 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12695 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052494759490 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12695) ≤ 0.010599231582 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12695 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035816334179)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010599231582 + 2 * 0.737676 / 12695) := by gcongr
    _ ≤ (0.052494759490 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12695 12 ≤ 0.0015 := by
  exact BstLean.Part269.S13.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12695

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12695
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560503342087 : ℝ) ≤ plow 12695 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12695) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052770528131)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001380937837) : eMP 12695 0.011 xi bn ≤ 0.001188852787 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12695 : ℝ) * (1 - 0.011))) ≤ 0.000587824289 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001380937837 / (12695 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000587824289 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000587824289 : ℝ) + 3.141593 * 0.052770528131 / (12695 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001188852787 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052770528131)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001380937837) : PiBarMP 12695 12 0.011 xi bn ≤ 0.161283086158 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12695 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037160971960 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.050680497710 : ℝ) ≤ √((12695 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.672090599225 : ℝ) ≤ √(12695 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12695) ≤ 0.123654475467 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037160971960 + 0.052770528131 * 1.772454 / (2 * (112.050680497710 : ℝ))) * (1 + 0.001188852787) +
        8 / (12695 * 112.672090599225) + 0.123654475467 := by gcongr
    _ ≤ (0.161283086158 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052770528131)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001380937837) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282213126477) :
    parallelOracle 12695 0.011 xi bn cd ≤ 0.162274015232 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12695 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12695 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560503342087 : ℝ) ≤ plow 12695 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.672090599225 : ℝ) ≤ √(12695 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282213126477 : ℝ) / (2 * 0.560503342087 * 112.672090599225)) * 0.161283086158 +
        0.282213126477 ^ 2 / (2 * 0.560503342087 * 112.672090599225) := by gcongr
    _ ≤ (0.162274015232 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052770528131) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001380937837)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282213126477) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12695 12695 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560503342087 : ℝ) ≤ plow 12695 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.672090599225 : ℝ) ≤ √(12695 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12695 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12695 Θ 1.22 ≤ 0.011769556178 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.672090599225 := by gcongr <;> linarith
      _ ≤ (0.011769556178 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12695 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12695 12695 0.011 ≤ 0.008483795991 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12695 12695 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12695 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12695 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12695 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12695 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162274015232 + 0.011769556178 + (0.008483795991 : ℝ) *
        (1 + 2 * (0.282213126477 + 0.011769556178) / (0.560503342087 * 112.672090599225))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12695]

end BstLean.Part269.N12695

/-! The original eight local profiles supply actual 12695 moment certificates. -/
namespace BstLean.Part269.N12695
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12695 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12695 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12695 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052770528131 ∧
    0 ≤ bN 12695 BstLean.Part154.csC (groupTheta g) ∧ bN 12695 BstLean.Part154.csC (groupTheta g) ≤ 0.001380937837 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12695 12695 0.011
      (momentAllowance 12695 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12695 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12695 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12695 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12695 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12695 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229718366987 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12695 0.011
      (momentAllowance 12695 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12695 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12695
/-! The actual computed-centre upper energy formula at 12695. -/
namespace BstLean.Part269.N12695
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12695

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12695
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12695)
open BstLean.Part268 (cell12695)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085504851256
  | 2 => 0.086447868971
  | 3 => 0.087389065527
  | 4 => 0.088329868014
  | 5 => 0.089272002278
  | 6 => 0.090217537256
  | 7 => 0.091168933475
  | 8 => 0.092129095761
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12695 12695 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12695 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003538895953 + 0.003300387184 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S13.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12695

/-! Actual upper energy certificates on all 43 source endpoints at 12695. -/
namespace BstLean.Part269.N12695
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12695)
open BstLean.Part268 (cell12695)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12695 (gMinus 12695) (1 - (cell12695 i).lower) ≤ 1 ∧
    energyUpper 12695 (gMinus 12695) (BstLean.Part211.gPlus 12695)
      (finiteEnergy 12695 12695 0.011) (1 - (cell12695 i).lower) ≤
      (cell12695 i).energy := by
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
      have E := BstLean.Part269.S13.uniformEnergy10 (n := 12695) (by norm_num)
        (q := 1 - (cell12695 ⟨10,by decide⟩).lower)
        (by norm_num [cell12695]) (by norm_num [cell12695])
      exact ⟨E.1,E.2.trans (by norm_num [cell12695])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy11 (n := 12695) (by norm_num)
        (q := 1 - (cell12695 ⟨11,by decide⟩).lower)
        (by norm_num [cell12695]) (by norm_num [cell12695])
      exact ⟨E.1,E.2.trans (by norm_num [cell12695])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy12 (n := 12695) (by norm_num)
        (q := 1 - (cell12695 ⟨12,by decide⟩).lower)
        (by norm_num [cell12695]) (by norm_num [cell12695])
      exact ⟨E.1,E.2.trans (by norm_num [cell12695])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy13 (n := 12695) (by norm_num)
        (q := 1 - (cell12695 ⟨13,by decide⟩).lower)
        (by norm_num [cell12695]) (by norm_num [cell12695])
      exact ⟨E.1,E.2.trans (by norm_num [cell12695])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy14 (n := 12695) (by norm_num)
        (q := 1 - (cell12695 ⟨14,by decide⟩).lower)
        (by norm_num [cell12695]) (by norm_num [cell12695])
      exact ⟨E.1,E.2.trans (by norm_num [cell12695])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy15 (n := 12695) (by norm_num)
        (q := 1 - (cell12695 ⟨15,by decide⟩).lower)
        (by norm_num [cell12695]) (by norm_num [cell12695])
      exact ⟨E.1,E.2.trans (by norm_num [cell12695])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy16 (n := 12695) (by norm_num)
        (q := 1 - (cell12695 ⟨16,by decide⟩).lower)
        (by norm_num [cell12695]) (by norm_num [cell12695])
      exact ⟨E.1,E.2.trans (by norm_num [cell12695])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy17 (n := 12695) (by norm_num)
        (q := 1 - (cell12695 ⟨17,by decide⟩).lower)
        (by norm_num [cell12695]) (by norm_num [cell12695])
      exact ⟨E.1,E.2.trans (by norm_num [cell12695])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy18 (n := 12695) (by norm_num)
        (q := 1 - (cell12695 ⟨18,by decide⟩).lower)
        (by norm_num [cell12695]) (by norm_num [cell12695])
      exact ⟨E.1,E.2.trans (by norm_num [cell12695])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy19 (n := 12695) (by norm_num)
        (q := 1 - (cell12695 ⟨19,by decide⟩).lower)
        (by norm_num [cell12695]) (by norm_num [cell12695])
      exact ⟨E.1,E.2.trans (by norm_num [cell12695])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy20 (n := 12695) (by norm_num)
        (q := 1 - (cell12695 ⟨20,by decide⟩).lower)
        (by norm_num [cell12695]) (by norm_num [cell12695])
      exact ⟨E.1,E.2.trans (by norm_num [cell12695])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy21 (n := 12695) (by norm_num)
        (q := 1 - (cell12695 ⟨21,by decide⟩).lower)
        (by norm_num [cell12695]) (by norm_num [cell12695])
      exact ⟨E.1,E.2.trans (by norm_num [cell12695])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy22 (n := 12695) (by norm_num)
        (q := 1 - (cell12695 ⟨22,by decide⟩).lower)
        (by norm_num [cell12695]) (by norm_num [cell12695])
      exact ⟨E.1,E.2.trans (by norm_num [cell12695])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy23 (n := 12695) (by norm_num)
        (q := 1 - (cell12695 ⟨23,by decide⟩).lower)
        (by norm_num [cell12695]) (by norm_num [cell12695])
      exact ⟨E.1,E.2.trans (by norm_num [cell12695])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy24 (n := 12695) (by norm_num)
        (q := 1 - (cell12695 ⟨24,by decide⟩).lower)
        (by norm_num [cell12695]) (by norm_num [cell12695])
      exact ⟨E.1,E.2.trans (by norm_num [cell12695])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy25 (n := 12695) (by norm_num)
        (q := 1 - (cell12695 ⟨25,by decide⟩).lower)
        (by norm_num [cell12695]) (by norm_num [cell12695])
      exact ⟨E.1,E.2.trans (by norm_num [cell12695])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy26 (n := 12695) (by norm_num)
        (q := 1 - (cell12695 ⟨26,by decide⟩).lower)
        (by norm_num [cell12695]) (by norm_num [cell12695])
      exact ⟨E.1,E.2.trans (by norm_num [cell12695])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy27 (n := 12695) (by norm_num)
        (q := 1 - (cell12695 ⟨27,by decide⟩).lower)
        (by norm_num [cell12695]) (by norm_num [cell12695])
      exact ⟨E.1,E.2.trans (by norm_num [cell12695])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy28 (n := 12695) (by norm_num)
        (q := 1 - (cell12695 ⟨28,by decide⟩).lower)
        (by norm_num [cell12695]) (by norm_num [cell12695])
      exact ⟨E.1,E.2.trans (by norm_num [cell12695])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy29 (n := 12695) (by norm_num)
        (q := 1 - (cell12695 ⟨29,by decide⟩).lower)
        (by norm_num [cell12695]) (by norm_num [cell12695])
      exact ⟨E.1,E.2.trans (by norm_num [cell12695])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy30 (n := 12695) (by norm_num)
        (q := 1 - (cell12695 ⟨30,by decide⟩).lower)
        (by norm_num [cell12695]) (by norm_num [cell12695])
      exact ⟨E.1,E.2.trans (by norm_num [cell12695])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy31 (n := 12695) (by norm_num)
        (q := 1 - (cell12695 ⟨31,by decide⟩).lower)
        (by norm_num [cell12695]) (by norm_num [cell12695])
      exact ⟨E.1,E.2.trans (by norm_num [cell12695])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy32 (n := 12695) (by norm_num)
        (q := 1 - (cell12695 ⟨32,by decide⟩).lower)
        (by norm_num [cell12695]) (by norm_num [cell12695])
      exact ⟨E.1,E.2.trans (by norm_num [cell12695])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy33 (n := 12695) (by norm_num)
        (q := 1 - (cell12695 ⟨33,by decide⟩).lower)
        (by norm_num [cell12695]) (by norm_num [cell12695])
      exact ⟨E.1,E.2.trans (by norm_num [cell12695])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy34 (n := 12695) (by norm_num)
        (q := 1 - (cell12695 ⟨34,by decide⟩).lower)
        (by norm_num [cell12695]) (by norm_num [cell12695])
      exact ⟨E.1,E.2.trans (by norm_num [cell12695])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy35 (n := 12695) (by norm_num)
        (q := 1 - (cell12695 ⟨35,by decide⟩).lower)
        (by norm_num [cell12695]) (by norm_num [cell12695])
      exact ⟨E.1,E.2.trans (by norm_num [cell12695])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy36 (n := 12695) (by norm_num)
        (q := 1 - (cell12695 ⟨36,by decide⟩).lower)
        (by norm_num [cell12695]) (by norm_num [cell12695])
      exact ⟨E.1,E.2.trans (by norm_num [cell12695])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy37 (n := 12695) (by norm_num)
        (q := 1 - (cell12695 ⟨37,by decide⟩).lower)
        (by norm_num [cell12695]) (by norm_num [cell12695])
      exact ⟨E.1,E.2.trans (by norm_num [cell12695])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy38 (n := 12695) (by norm_num)
        (q := 1 - (cell12695 ⟨38,by decide⟩).lower)
        (by norm_num [cell12695]) (by norm_num [cell12695])
      exact ⟨E.1,E.2.trans (by norm_num [cell12695])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy39 (n := 12695) (by norm_num)
        (q := 1 - (cell12695 ⟨39,by decide⟩).lower)
        (by norm_num [cell12695]) (by norm_num [cell12695])
      exact ⟨E.1,E.2.trans (by norm_num [cell12695])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy40 (n := 12695) (by norm_num)
        (q := 1 - (cell12695 ⟨40,by decide⟩).lower)
        (by norm_num [cell12695]) (by norm_num [cell12695])
      exact ⟨E.1,E.2.trans (by norm_num [cell12695])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy41 (n := 12695) (by norm_num)
        (q := 1 - (cell12695 ⟨41,by decide⟩).lower)
        (by norm_num [cell12695]) (by norm_num [cell12695])
      exact ⟨E.1,E.2.trans (by norm_num [cell12695])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy42 (n := 12695) (by norm_num)
        (q := 1 - (cell12695 ⟨42,by decide⟩).lower)
        (by norm_num [cell12695]) (by norm_num [cell12695])
      exact ⟨E.1,E.2.trans (by norm_num [cell12695])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy43 (n := 12695) (by norm_num)
        (q := 1 - (cell12695 ⟨43,by decide⟩).lower)
        (by norm_num [cell12695]) (by norm_num [cell12695])
      exact ⟨E.1,E.2.trans (by norm_num [cell12695])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy44 (n := 12695) (by norm_num)
        (q := 1 - (cell12695 ⟨44,by decide⟩).lower)
        (by norm_num [cell12695]) (by norm_num [cell12695])
      exact ⟨E.1,E.2.trans (by norm_num [cell12695])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy45 (n := 12695) (by norm_num)
        (q := 1 - (cell12695 ⟨45,by decide⟩).lower)
        (by norm_num [cell12695]) (by norm_num [cell12695])
      exact ⟨E.1,E.2.trans (by norm_num [cell12695])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy46 (n := 12695) (by norm_num)
        (q := 1 - (cell12695 ⟨46,by decide⟩).lower)
        (by norm_num [cell12695]) (by norm_num [cell12695])
      exact ⟨E.1,E.2.trans (by norm_num [cell12695])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy47 (n := 12695) (by norm_num)
        (q := 1 - (cell12695 ⟨47,by decide⟩).lower)
        (by norm_num [cell12695]) (by norm_num [cell12695])
      exact ⟨E.1,E.2.trans (by norm_num [cell12695])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy48 (n := 12695) (by norm_num)
        (q := 1 - (cell12695 ⟨48,by decide⟩).lower)
        (by norm_num [cell12695]) (by norm_num [cell12695])
      exact ⟨E.1,E.2.trans (by norm_num [cell12695])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy49 (n := 12695) (by norm_num)
        (q := 1 - (cell12695 ⟨49,by decide⟩).lower)
        (by norm_num [cell12695]) (by norm_num [cell12695])
      exact ⟨E.1,E.2.trans (by norm_num [cell12695])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy50 (n := 12695) (by norm_num)
        (q := 1 - (cell12695 ⟨50,by decide⟩).lower)
        (by norm_num [cell12695]) (by norm_num [cell12695])
      exact ⟨E.1,E.2.trans (by norm_num [cell12695])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy51 (n := 12695) (by norm_num)
        (q := 1 - (cell12695 ⟨51,by decide⟩).lower)
        (by norm_num [cell12695]) (by norm_num [cell12695])
      exact ⟨E.1,E.2.trans (by norm_num [cell12695])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy52 (n := 12695) (by norm_num)
        (q := 1 - (cell12695 ⟨52,by decide⟩).lower)
        (by norm_num [cell12695]) (by norm_num [cell12695])
      exact ⟨E.1,E.2.trans (by norm_num [cell12695])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12695

/-! Source-cell containment and simple scalar guards at 12695. -/
namespace BstLean.Part269.N12695
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12695)
open BstLean.Part268 (cell12695)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12695 ⟨10,by decide⟩).lower ∧ (cell12695 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12695 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12695 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12695 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12695 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12695 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12695,cell12695,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12695 ⟨11,by decide⟩).lower ∧ (cell12695 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12695 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12695 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12695 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12695 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12695 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12695,cell12695,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12695 ⟨12,by decide⟩).lower ∧ (cell12695 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12695 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12695 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12695 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12695 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12695 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12695,cell12695,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12695 ⟨13,by decide⟩).lower ∧ (cell12695 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12695 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12695 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12695 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12695 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12695 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12695,cell12695,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12695 ⟨14,by decide⟩).lower ∧ (cell12695 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12695 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12695 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12695 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12695 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12695 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12695,cell12695,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12695 ⟨15,by decide⟩).lower ∧ (cell12695 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12695 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12695 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12695 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12695 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12695 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12695,cell12695,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12695 ⟨16,by decide⟩).lower ∧ (cell12695 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12695 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12695 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12695 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12695 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12695 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12695,cell12695,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12695 ⟨17,by decide⟩).lower ∧ (cell12695 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12695 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12695 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12695 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12695 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12695 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12695,cell12695,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12695 ⟨18,by decide⟩).lower ∧ (cell12695 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12695 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12695 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12695 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12695 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12695 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12695,cell12695,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12695 ⟨19,by decide⟩).lower ∧ (cell12695 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12695 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12695 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12695 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12695 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12695 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12695,cell12695,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12695 ⟨20,by decide⟩).lower ∧ (cell12695 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12695 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12695 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12695 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12695 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12695 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12695,cell12695,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12695 ⟨21,by decide⟩).lower ∧ (cell12695 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12695 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12695 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12695 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12695 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12695 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12695,cell12695,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12695 ⟨22,by decide⟩).lower ∧ (cell12695 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12695 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12695 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12695 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12695 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12695 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12695,cell12695,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12695 ⟨23,by decide⟩).lower ∧ (cell12695 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12695 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12695 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12695 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12695 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12695 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12695,cell12695,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12695 ⟨24,by decide⟩).lower ∧ (cell12695 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12695 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12695 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12695 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12695 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12695 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12695,cell12695,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12695 ⟨25,by decide⟩).lower ∧ (cell12695 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12695 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12695 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12695 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12695 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12695 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12695,cell12695,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12695 ⟨26,by decide⟩).lower ∧ (cell12695 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12695 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12695 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12695 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12695 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12695 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12695,cell12695,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12695 ⟨27,by decide⟩).lower ∧ (cell12695 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12695 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12695 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12695 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12695 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12695 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12695,cell12695,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12695 ⟨28,by decide⟩).lower ∧ (cell12695 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12695 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12695 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12695 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12695 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12695 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12695,cell12695,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12695 ⟨29,by decide⟩).lower ∧ (cell12695 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12695 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12695 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12695 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12695 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12695 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12695,cell12695,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12695 ⟨30,by decide⟩).lower ∧ (cell12695 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12695 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12695 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12695 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12695 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12695 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12695,cell12695,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12695 ⟨31,by decide⟩).lower ∧ (cell12695 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12695 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12695 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12695 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12695 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12695 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12695,cell12695,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12695 ⟨32,by decide⟩).lower ∧ (cell12695 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12695 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12695 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12695 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12695 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12695 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12695,cell12695,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12695 ⟨33,by decide⟩).lower ∧ (cell12695 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12695 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12695 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12695 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12695 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12695 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12695,cell12695,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12695 ⟨34,by decide⟩).lower ∧ (cell12695 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12695 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12695 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12695 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12695 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12695 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12695,cell12695,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12695 ⟨35,by decide⟩).lower ∧ (cell12695 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12695 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12695 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12695 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12695 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12695 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12695,cell12695,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12695 ⟨36,by decide⟩).lower ∧ (cell12695 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12695 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12695 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12695 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12695 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12695 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12695,cell12695,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12695 ⟨37,by decide⟩).lower ∧ (cell12695 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12695 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12695 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12695 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12695 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12695 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12695,cell12695,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12695 ⟨38,by decide⟩).lower ∧ (cell12695 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12695 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12695 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12695 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12695 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12695 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12695,cell12695,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12695 ⟨39,by decide⟩).lower ∧ (cell12695 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12695 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12695 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12695 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12695 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12695 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12695,cell12695,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12695 ⟨40,by decide⟩).lower ∧ (cell12695 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12695 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12695 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12695 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12695 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12695 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12695,cell12695,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12695 ⟨41,by decide⟩).lower ∧ (cell12695 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12695 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12695 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12695 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12695 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12695 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12695,cell12695,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12695 ⟨42,by decide⟩).lower ∧ (cell12695 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12695 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12695 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12695 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12695 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12695 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12695,cell12695,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12695 ⟨43,by decide⟩).lower ∧ (cell12695 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12695 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12695 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12695 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12695 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12695 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12695,cell12695,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12695 ⟨44,by decide⟩).lower ∧ (cell12695 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12695 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12695 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12695 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12695 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12695 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12695,cell12695,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12695 ⟨45,by decide⟩).lower ∧ (cell12695 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12695 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12695 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12695 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12695 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12695 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12695,cell12695,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12695 ⟨46,by decide⟩).lower ∧ (cell12695 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12695 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12695 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12695 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12695 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12695 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12695,cell12695,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12695 ⟨47,by decide⟩).lower ∧ (cell12695 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12695 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12695 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12695 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12695 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12695 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12695,cell12695,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12695 ⟨48,by decide⟩).lower ∧ (cell12695 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12695 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12695 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12695 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12695 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12695 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12695,cell12695,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12695 ⟨49,by decide⟩).lower ∧ (cell12695 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12695 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12695 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12695 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12695 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12695 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12695,cell12695,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12695 ⟨50,by decide⟩).lower ∧ (cell12695 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12695 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12695 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12695 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12695 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12695 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12695,cell12695,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12695 ⟨51,by decide⟩).lower ∧ (cell12695 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12695 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12695 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12695 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12695 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12695 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12695,cell12695,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12695 ⟨52,by decide⟩).lower ∧ (cell12695 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12695 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12695 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12695 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12695 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12695 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12695,cell12695,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12695 i).lower ∧
    (cell12695 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12695 i).upper ≤ (0.532 : ℝ) ∧
    (cell12695 i).centre ≤ (0.1 : ℝ) ∧ (cell12695 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12695 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12695 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12695

/-! The local source numeric instances at 12695 have no network premises. -/
namespace BstLean.Part269.N12695
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12695)
open BstLean.Part268 (cell12695)

noncomputable def sourceNumerics12695 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12695 (cell12695 i)
      scalarRow12695.M scalarRow12695.H scalarRow12695.xi := by
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
    energy_allowance := scalarRow12695.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12695]
    centre_nonneg := (scalarRow12695.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D13.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12695])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12695
/-! Actual 12696 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12696
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12696 ≤ (1.035814911207 : ℝ) := by
  have hr : (112.676528168026 : ℝ) ≤ √(12696 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.676528168026 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12696 12696 (11 / 1000) ≤
    (0.008483461869 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12696) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.676528168026 : ℝ) ≤ √(12696 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12696)
  have hdiv : K / √(12696 : ℝ) ≤ K / 112.676528168026 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.676528168026 ≤ (0.008483461869 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12696.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12696 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12696 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12696 := gPlus_lower 12696
end BstLean.Part269.N12696

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12696
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035814911206 : ℝ) ≤ wn 12696 := by
  have hn : √(12696 : ℝ) ≤ 112.676528168027 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12696 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.676528168027 ≤ 2 / √(12696 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000251961611 : ℝ) ≤ rhoBar 12696 BstLean.Part154.csC ∧
    rhoBar 12696 BstLean.Part154.csC ≤ 0.000251962001 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035814911206 : ℝ) / (1.295212 * 12696) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035814911207 : ℝ) / (1.29521 * 12696) := by gcongr
      _ ≤ (0.000251962001 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12696 BstLean.Part154.csC) ≤ 0.001007911489 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12696 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12696 BstLean.Part154.csC) (piBar (rhoBar 12696 BstLean.Part154.csC)) ≤ 0.000192450279 ∧
    cc1 (rhoBar 12696 BstLean.Part154.csC) (piBar (rhoBar 12696 BstLean.Part154.csC)) ≤ 0.000122457390 ∧
    cc2 (rhoBar 12696 BstLean.Part154.csC) ≤ 0.000071087452 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12696 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12696 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12696 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12696 BstLean.Part154.csC * nuR (rhoBar 12696 BstLean.Part154.csC)) ≤ 0.000503939874 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000251962001 : ℝ) * 0.001007911489 := by gcongr
      _ ≤ (0.000503939874 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12696 BstLean.Part154.csC) * nuR (rhoBar 12696 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001007911489 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12696 BstLean.Part154.csC) * rhoBar 12696 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000251962001 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000251962001 / 2 + 0.399 * 0.001007911489 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000192450279 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000503939874 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122457390 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000251962001 / 1.414213562 := by gcongr
      _ ≤ (0.000071087452 : ℝ) := by norm_num

end BstLean.Part269.N12696

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12696
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12696 BstLean.Part154.csC) (piBar (rhoBar 12696 BstLean.Part154.csC)) ≤ 1.59946E-7 := by
  have hr0 : 0 ≤ rhoBar 12696 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12696 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12696 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12696 BstLean.Part154.csC) (piBar (rhoBar 12696 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12696 BstLean.Part154.csC) (piBar (rhoBar 12696 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12696 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000192450279 : ℝ) ^ 2 + 0.000122457390 ^ 2 + 3 * 0.000071087452 ^ 2 +
        2 * 0.797885 * 0.000192450279 * 0.000122457390 + 2 * 0.000192450279 * 0.000071087452 +
        4 * 0.797885 * 0.000122457390 * 0.000071087452 := by gcongr
    _ ≤ (1.59946E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12696 BstLean.Part154.csC Θ ≤ 0.002630153874 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12696 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12696 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12696 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12696 BstLean.Part154.csC) (piBar (rhoBar 12696 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12696 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035814911207 * 1.59946E-7 / (0.000251961611 : ℝ) := by gcongr
    _ ≤ 0.002630153874 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12696 BstLean.Part154.csC Θ ≤ 0.002918305306 + 0.000664595525 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12696 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12696 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12696 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035814911207 : ℝ) * ((2 * Θ * 0.000251962001 +
        (6863 / 10000) * 0.000251962001 * 12696 * 0.001007911489) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002918305306 + 0.000664595525 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12696 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12696 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12696 0.011 Θ ∧ gammaRatio 12696 0.011 Θ ≤ 0.000086618021 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12696 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035814911207 : ℝ) * 0.525 / ((1 - 0.011) * 12696) := by gcongr
      _ ≤ (0.000086618021 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12696 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12696 0.011 Θ) :=
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
    badAllowance 12696 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000615501984 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12696 BstLean.Part154.csC) 1.22 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 2 (rhoBar 12696 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12696 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12696 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12696 0.011 Θ) 1.12 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 1 (gammaRatio 12696 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12696 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12696 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12696 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12696 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035814911207 : ℝ) * 12696 *
        (2.2721E-8 / 1.1045361 + 2.7751E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000615501984 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12696 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003533807290 + 0.003294749399 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12696

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12696
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12696 BstLean.Part154.csC) (piBar (rhoBar 12696 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12696 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12696 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12696 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12696 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12696 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12696 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12696 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12696 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12696 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12696 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12696 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12696 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12696 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12696 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052492669656 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12696) ≤ 0.010598814150 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12696 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035814911207)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010598814150 + 2 * 0.737676 / 12696) := by gcongr
    _ ≤ (0.052492669656 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12696 12 ≤ 0.0015 := by
  exact BstLean.Part269.S13.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12696

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12696
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560503387342 : ℝ) ≤ plow 12696 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12696) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052770150725)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001380830784) : eMP 12696 0.011 xi bn ≤ 0.001188759782 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12696 : ℝ) * (1 - 0.011))) ≤ 0.000587778354 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001380830784 / (12696 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000587778354 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000587778354 : ℝ) + 3.141593 * 0.052770150725 / (12696 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001188759782 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052770150725)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001380830784) : PiBarMP 12696 12 0.011 xi bn ≤ 0.161276750506 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12696 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037159531537 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.055093592393 : ℝ) ≤ √((12696 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.676528168026 : ℝ) ≤ √(12696 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12696) ≤ 0.123649605551 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037159531537 + 0.052770150725 * 1.772454 / (2 * (112.055093592393 : ℝ))) * (1 + 0.001188759782) +
        8 / (12696 * 112.676528168026) + 0.123649605551 := by gcongr
    _ ≤ (0.161276750506 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052770150725)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001380830784) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282210215188) :
    parallelOracle 12696 0.011 xi bn cd ≤ 0.162267609592 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12696 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12696 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560503387342 : ℝ) ≤ plow 12696 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.676528168026 : ℝ) ≤ √(12696 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282210215188 : ℝ) / (2 * 0.560503387342 * 112.676528168026)) * 0.161276750506 +
        0.282210215188 ^ 2 / (2 * 0.560503387342 * 112.676528168026) := by gcongr
    _ ≤ (0.162267609592 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052770150725) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001380830784)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282210215188) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12696 12696 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560503387342 : ℝ) ≤ plow 12696 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.676528168026 : ℝ) ≤ √(12696 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12696 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12696 Θ 1.22 ≤ 0.011769092655 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.676528168026 := by gcongr <;> linarith
      _ ≤ (0.011769092655 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12696 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12696 12696 0.011 ≤ 0.008483461869 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12696 12696 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12696 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12696 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12696 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12696 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162267609592 + 0.011769092655 + (0.008483461869 : ℝ) *
        (1 + 2 * (0.282210215188 + 0.011769092655) / (0.560503387342 * 112.676528168026))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12696]

end BstLean.Part269.N12696

/-! The original eight local profiles supply actual 12696 moment certificates. -/
namespace BstLean.Part269.N12696
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12696 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12696 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12696 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052770150725 ∧
    0 ≤ bN 12696 BstLean.Part154.csC (groupTheta g) ∧ bN 12696 BstLean.Part154.csC (groupTheta g) ≤ 0.001380830784 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12696 12696 0.011
      (momentAllowance 12696 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12696 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12696 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12696 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12696 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12696 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229717545532 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12696 0.011
      (momentAllowance 12696 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12696 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12696
/-! The actual computed-centre upper energy formula at 12696. -/
namespace BstLean.Part269.N12696
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12696

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12696
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12696)
open BstLean.Part268 (cell12696)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085501930073
  | 2 => 0.086444894008
  | 3 => 0.087386028921
  | 4 => 0.088326760092
  | 5 => 0.089268811237
  | 6 => 0.090214248803
  | 7 => 0.091165530431
  | 8 => 0.092125557609
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12696 12696 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12696 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003538895953 + 0.003300387184 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S13.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12696

/-! Actual upper energy certificates on all 43 source endpoints at 12696. -/
namespace BstLean.Part269.N12696
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12696)
open BstLean.Part268 (cell12696)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12696 (gMinus 12696) (1 - (cell12696 i).lower) ≤ 1 ∧
    energyUpper 12696 (gMinus 12696) (BstLean.Part211.gPlus 12696)
      (finiteEnergy 12696 12696 0.011) (1 - (cell12696 i).lower) ≤
      (cell12696 i).energy := by
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
      have E := BstLean.Part269.S13.uniformEnergy10 (n := 12696) (by norm_num)
        (q := 1 - (cell12696 ⟨10,by decide⟩).lower)
        (by norm_num [cell12696]) (by norm_num [cell12696])
      exact ⟨E.1,E.2.trans (by norm_num [cell12696])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy11 (n := 12696) (by norm_num)
        (q := 1 - (cell12696 ⟨11,by decide⟩).lower)
        (by norm_num [cell12696]) (by norm_num [cell12696])
      exact ⟨E.1,E.2.trans (by norm_num [cell12696])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy12 (n := 12696) (by norm_num)
        (q := 1 - (cell12696 ⟨12,by decide⟩).lower)
        (by norm_num [cell12696]) (by norm_num [cell12696])
      exact ⟨E.1,E.2.trans (by norm_num [cell12696])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy13 (n := 12696) (by norm_num)
        (q := 1 - (cell12696 ⟨13,by decide⟩).lower)
        (by norm_num [cell12696]) (by norm_num [cell12696])
      exact ⟨E.1,E.2.trans (by norm_num [cell12696])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy14 (n := 12696) (by norm_num)
        (q := 1 - (cell12696 ⟨14,by decide⟩).lower)
        (by norm_num [cell12696]) (by norm_num [cell12696])
      exact ⟨E.1,E.2.trans (by norm_num [cell12696])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy15 (n := 12696) (by norm_num)
        (q := 1 - (cell12696 ⟨15,by decide⟩).lower)
        (by norm_num [cell12696]) (by norm_num [cell12696])
      exact ⟨E.1,E.2.trans (by norm_num [cell12696])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy16 (n := 12696) (by norm_num)
        (q := 1 - (cell12696 ⟨16,by decide⟩).lower)
        (by norm_num [cell12696]) (by norm_num [cell12696])
      exact ⟨E.1,E.2.trans (by norm_num [cell12696])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy17 (n := 12696) (by norm_num)
        (q := 1 - (cell12696 ⟨17,by decide⟩).lower)
        (by norm_num [cell12696]) (by norm_num [cell12696])
      exact ⟨E.1,E.2.trans (by norm_num [cell12696])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy18 (n := 12696) (by norm_num)
        (q := 1 - (cell12696 ⟨18,by decide⟩).lower)
        (by norm_num [cell12696]) (by norm_num [cell12696])
      exact ⟨E.1,E.2.trans (by norm_num [cell12696])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy19 (n := 12696) (by norm_num)
        (q := 1 - (cell12696 ⟨19,by decide⟩).lower)
        (by norm_num [cell12696]) (by norm_num [cell12696])
      exact ⟨E.1,E.2.trans (by norm_num [cell12696])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy20 (n := 12696) (by norm_num)
        (q := 1 - (cell12696 ⟨20,by decide⟩).lower)
        (by norm_num [cell12696]) (by norm_num [cell12696])
      exact ⟨E.1,E.2.trans (by norm_num [cell12696])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy21 (n := 12696) (by norm_num)
        (q := 1 - (cell12696 ⟨21,by decide⟩).lower)
        (by norm_num [cell12696]) (by norm_num [cell12696])
      exact ⟨E.1,E.2.trans (by norm_num [cell12696])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy22 (n := 12696) (by norm_num)
        (q := 1 - (cell12696 ⟨22,by decide⟩).lower)
        (by norm_num [cell12696]) (by norm_num [cell12696])
      exact ⟨E.1,E.2.trans (by norm_num [cell12696])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy23 (n := 12696) (by norm_num)
        (q := 1 - (cell12696 ⟨23,by decide⟩).lower)
        (by norm_num [cell12696]) (by norm_num [cell12696])
      exact ⟨E.1,E.2.trans (by norm_num [cell12696])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy24 (n := 12696) (by norm_num)
        (q := 1 - (cell12696 ⟨24,by decide⟩).lower)
        (by norm_num [cell12696]) (by norm_num [cell12696])
      exact ⟨E.1,E.2.trans (by norm_num [cell12696])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy25 (n := 12696) (by norm_num)
        (q := 1 - (cell12696 ⟨25,by decide⟩).lower)
        (by norm_num [cell12696]) (by norm_num [cell12696])
      exact ⟨E.1,E.2.trans (by norm_num [cell12696])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy26 (n := 12696) (by norm_num)
        (q := 1 - (cell12696 ⟨26,by decide⟩).lower)
        (by norm_num [cell12696]) (by norm_num [cell12696])
      exact ⟨E.1,E.2.trans (by norm_num [cell12696])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy27 (n := 12696) (by norm_num)
        (q := 1 - (cell12696 ⟨27,by decide⟩).lower)
        (by norm_num [cell12696]) (by norm_num [cell12696])
      exact ⟨E.1,E.2.trans (by norm_num [cell12696])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy28 (n := 12696) (by norm_num)
        (q := 1 - (cell12696 ⟨28,by decide⟩).lower)
        (by norm_num [cell12696]) (by norm_num [cell12696])
      exact ⟨E.1,E.2.trans (by norm_num [cell12696])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy29 (n := 12696) (by norm_num)
        (q := 1 - (cell12696 ⟨29,by decide⟩).lower)
        (by norm_num [cell12696]) (by norm_num [cell12696])
      exact ⟨E.1,E.2.trans (by norm_num [cell12696])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy30 (n := 12696) (by norm_num)
        (q := 1 - (cell12696 ⟨30,by decide⟩).lower)
        (by norm_num [cell12696]) (by norm_num [cell12696])
      exact ⟨E.1,E.2.trans (by norm_num [cell12696])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy31 (n := 12696) (by norm_num)
        (q := 1 - (cell12696 ⟨31,by decide⟩).lower)
        (by norm_num [cell12696]) (by norm_num [cell12696])
      exact ⟨E.1,E.2.trans (by norm_num [cell12696])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy32 (n := 12696) (by norm_num)
        (q := 1 - (cell12696 ⟨32,by decide⟩).lower)
        (by norm_num [cell12696]) (by norm_num [cell12696])
      exact ⟨E.1,E.2.trans (by norm_num [cell12696])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy33 (n := 12696) (by norm_num)
        (q := 1 - (cell12696 ⟨33,by decide⟩).lower)
        (by norm_num [cell12696]) (by norm_num [cell12696])
      exact ⟨E.1,E.2.trans (by norm_num [cell12696])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy34 (n := 12696) (by norm_num)
        (q := 1 - (cell12696 ⟨34,by decide⟩).lower)
        (by norm_num [cell12696]) (by norm_num [cell12696])
      exact ⟨E.1,E.2.trans (by norm_num [cell12696])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy35 (n := 12696) (by norm_num)
        (q := 1 - (cell12696 ⟨35,by decide⟩).lower)
        (by norm_num [cell12696]) (by norm_num [cell12696])
      exact ⟨E.1,E.2.trans (by norm_num [cell12696])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy36 (n := 12696) (by norm_num)
        (q := 1 - (cell12696 ⟨36,by decide⟩).lower)
        (by norm_num [cell12696]) (by norm_num [cell12696])
      exact ⟨E.1,E.2.trans (by norm_num [cell12696])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy37 (n := 12696) (by norm_num)
        (q := 1 - (cell12696 ⟨37,by decide⟩).lower)
        (by norm_num [cell12696]) (by norm_num [cell12696])
      exact ⟨E.1,E.2.trans (by norm_num [cell12696])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy38 (n := 12696) (by norm_num)
        (q := 1 - (cell12696 ⟨38,by decide⟩).lower)
        (by norm_num [cell12696]) (by norm_num [cell12696])
      exact ⟨E.1,E.2.trans (by norm_num [cell12696])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy39 (n := 12696) (by norm_num)
        (q := 1 - (cell12696 ⟨39,by decide⟩).lower)
        (by norm_num [cell12696]) (by norm_num [cell12696])
      exact ⟨E.1,E.2.trans (by norm_num [cell12696])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy40 (n := 12696) (by norm_num)
        (q := 1 - (cell12696 ⟨40,by decide⟩).lower)
        (by norm_num [cell12696]) (by norm_num [cell12696])
      exact ⟨E.1,E.2.trans (by norm_num [cell12696])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy41 (n := 12696) (by norm_num)
        (q := 1 - (cell12696 ⟨41,by decide⟩).lower)
        (by norm_num [cell12696]) (by norm_num [cell12696])
      exact ⟨E.1,E.2.trans (by norm_num [cell12696])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy42 (n := 12696) (by norm_num)
        (q := 1 - (cell12696 ⟨42,by decide⟩).lower)
        (by norm_num [cell12696]) (by norm_num [cell12696])
      exact ⟨E.1,E.2.trans (by norm_num [cell12696])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy43 (n := 12696) (by norm_num)
        (q := 1 - (cell12696 ⟨43,by decide⟩).lower)
        (by norm_num [cell12696]) (by norm_num [cell12696])
      exact ⟨E.1,E.2.trans (by norm_num [cell12696])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy44 (n := 12696) (by norm_num)
        (q := 1 - (cell12696 ⟨44,by decide⟩).lower)
        (by norm_num [cell12696]) (by norm_num [cell12696])
      exact ⟨E.1,E.2.trans (by norm_num [cell12696])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy45 (n := 12696) (by norm_num)
        (q := 1 - (cell12696 ⟨45,by decide⟩).lower)
        (by norm_num [cell12696]) (by norm_num [cell12696])
      exact ⟨E.1,E.2.trans (by norm_num [cell12696])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy46 (n := 12696) (by norm_num)
        (q := 1 - (cell12696 ⟨46,by decide⟩).lower)
        (by norm_num [cell12696]) (by norm_num [cell12696])
      exact ⟨E.1,E.2.trans (by norm_num [cell12696])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy47 (n := 12696) (by norm_num)
        (q := 1 - (cell12696 ⟨47,by decide⟩).lower)
        (by norm_num [cell12696]) (by norm_num [cell12696])
      exact ⟨E.1,E.2.trans (by norm_num [cell12696])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy48 (n := 12696) (by norm_num)
        (q := 1 - (cell12696 ⟨48,by decide⟩).lower)
        (by norm_num [cell12696]) (by norm_num [cell12696])
      exact ⟨E.1,E.2.trans (by norm_num [cell12696])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy49 (n := 12696) (by norm_num)
        (q := 1 - (cell12696 ⟨49,by decide⟩).lower)
        (by norm_num [cell12696]) (by norm_num [cell12696])
      exact ⟨E.1,E.2.trans (by norm_num [cell12696])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy50 (n := 12696) (by norm_num)
        (q := 1 - (cell12696 ⟨50,by decide⟩).lower)
        (by norm_num [cell12696]) (by norm_num [cell12696])
      exact ⟨E.1,E.2.trans (by norm_num [cell12696])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy51 (n := 12696) (by norm_num)
        (q := 1 - (cell12696 ⟨51,by decide⟩).lower)
        (by norm_num [cell12696]) (by norm_num [cell12696])
      exact ⟨E.1,E.2.trans (by norm_num [cell12696])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy52 (n := 12696) (by norm_num)
        (q := 1 - (cell12696 ⟨52,by decide⟩).lower)
        (by norm_num [cell12696]) (by norm_num [cell12696])
      exact ⟨E.1,E.2.trans (by norm_num [cell12696])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12696

/-! Source-cell containment and simple scalar guards at 12696. -/
namespace BstLean.Part269.N12696
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12696)
open BstLean.Part268 (cell12696)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12696 ⟨10,by decide⟩).lower ∧ (cell12696 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12696 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12696 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12696 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12696 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12696 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12696,cell12696,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12696 ⟨11,by decide⟩).lower ∧ (cell12696 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12696 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12696 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12696 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12696 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12696 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12696,cell12696,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12696 ⟨12,by decide⟩).lower ∧ (cell12696 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12696 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12696 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12696 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12696 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12696 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12696,cell12696,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12696 ⟨13,by decide⟩).lower ∧ (cell12696 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12696 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12696 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12696 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12696 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12696 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12696,cell12696,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12696 ⟨14,by decide⟩).lower ∧ (cell12696 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12696 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12696 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12696 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12696 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12696 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12696,cell12696,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12696 ⟨15,by decide⟩).lower ∧ (cell12696 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12696 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12696 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12696 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12696 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12696 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12696,cell12696,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12696 ⟨16,by decide⟩).lower ∧ (cell12696 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12696 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12696 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12696 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12696 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12696 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12696,cell12696,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12696 ⟨17,by decide⟩).lower ∧ (cell12696 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12696 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12696 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12696 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12696 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12696 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12696,cell12696,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12696 ⟨18,by decide⟩).lower ∧ (cell12696 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12696 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12696 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12696 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12696 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12696 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12696,cell12696,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12696 ⟨19,by decide⟩).lower ∧ (cell12696 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12696 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12696 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12696 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12696 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12696 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12696,cell12696,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12696 ⟨20,by decide⟩).lower ∧ (cell12696 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12696 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12696 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12696 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12696 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12696 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12696,cell12696,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12696 ⟨21,by decide⟩).lower ∧ (cell12696 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12696 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12696 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12696 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12696 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12696 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12696,cell12696,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12696 ⟨22,by decide⟩).lower ∧ (cell12696 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12696 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12696 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12696 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12696 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12696 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12696,cell12696,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12696 ⟨23,by decide⟩).lower ∧ (cell12696 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12696 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12696 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12696 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12696 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12696 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12696,cell12696,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12696 ⟨24,by decide⟩).lower ∧ (cell12696 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12696 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12696 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12696 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12696 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12696 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12696,cell12696,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12696 ⟨25,by decide⟩).lower ∧ (cell12696 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12696 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12696 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12696 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12696 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12696 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12696,cell12696,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12696 ⟨26,by decide⟩).lower ∧ (cell12696 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12696 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12696 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12696 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12696 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12696 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12696,cell12696,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12696 ⟨27,by decide⟩).lower ∧ (cell12696 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12696 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12696 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12696 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12696 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12696 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12696,cell12696,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12696 ⟨28,by decide⟩).lower ∧ (cell12696 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12696 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12696 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12696 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12696 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12696 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12696,cell12696,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12696 ⟨29,by decide⟩).lower ∧ (cell12696 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12696 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12696 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12696 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12696 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12696 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12696,cell12696,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12696 ⟨30,by decide⟩).lower ∧ (cell12696 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12696 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12696 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12696 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12696 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12696 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12696,cell12696,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12696 ⟨31,by decide⟩).lower ∧ (cell12696 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12696 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12696 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12696 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12696 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12696 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12696,cell12696,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12696 ⟨32,by decide⟩).lower ∧ (cell12696 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12696 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12696 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12696 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12696 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12696 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12696,cell12696,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12696 ⟨33,by decide⟩).lower ∧ (cell12696 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12696 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12696 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12696 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12696 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12696 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12696,cell12696,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12696 ⟨34,by decide⟩).lower ∧ (cell12696 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12696 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12696 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12696 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12696 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12696 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12696,cell12696,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12696 ⟨35,by decide⟩).lower ∧ (cell12696 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12696 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12696 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12696 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12696 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12696 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12696,cell12696,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12696 ⟨36,by decide⟩).lower ∧ (cell12696 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12696 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12696 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12696 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12696 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12696 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12696,cell12696,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12696 ⟨37,by decide⟩).lower ∧ (cell12696 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12696 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12696 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12696 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12696 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12696 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12696,cell12696,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12696 ⟨38,by decide⟩).lower ∧ (cell12696 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12696 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12696 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12696 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12696 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12696 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12696,cell12696,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12696 ⟨39,by decide⟩).lower ∧ (cell12696 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12696 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12696 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12696 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12696 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12696 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12696,cell12696,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12696 ⟨40,by decide⟩).lower ∧ (cell12696 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12696 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12696 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12696 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12696 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12696 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12696,cell12696,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12696 ⟨41,by decide⟩).lower ∧ (cell12696 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12696 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12696 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12696 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12696 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12696 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12696,cell12696,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12696 ⟨42,by decide⟩).lower ∧ (cell12696 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12696 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12696 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12696 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12696 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12696 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12696,cell12696,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12696 ⟨43,by decide⟩).lower ∧ (cell12696 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12696 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12696 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12696 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12696 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12696 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12696,cell12696,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12696 ⟨44,by decide⟩).lower ∧ (cell12696 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12696 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12696 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12696 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12696 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12696 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12696,cell12696,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12696 ⟨45,by decide⟩).lower ∧ (cell12696 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12696 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12696 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12696 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12696 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12696 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12696,cell12696,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12696 ⟨46,by decide⟩).lower ∧ (cell12696 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12696 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12696 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12696 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12696 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12696 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12696,cell12696,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12696 ⟨47,by decide⟩).lower ∧ (cell12696 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12696 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12696 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12696 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12696 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12696 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12696,cell12696,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12696 ⟨48,by decide⟩).lower ∧ (cell12696 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12696 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12696 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12696 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12696 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12696 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12696,cell12696,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12696 ⟨49,by decide⟩).lower ∧ (cell12696 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12696 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12696 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12696 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12696 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12696 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12696,cell12696,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12696 ⟨50,by decide⟩).lower ∧ (cell12696 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12696 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12696 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12696 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12696 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12696 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12696,cell12696,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12696 ⟨51,by decide⟩).lower ∧ (cell12696 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12696 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12696 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12696 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12696 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12696 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12696,cell12696,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12696 ⟨52,by decide⟩).lower ∧ (cell12696 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12696 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12696 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12696 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12696 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12696 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12696,cell12696,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12696 i).lower ∧
    (cell12696 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12696 i).upper ≤ (0.532 : ℝ) ∧
    (cell12696 i).centre ≤ (0.1 : ℝ) ∧ (cell12696 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12696 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12696 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12696

/-! The local source numeric instances at 12696 have no network premises. -/
namespace BstLean.Part269.N12696
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12696)
open BstLean.Part268 (cell12696)

noncomputable def sourceNumerics12696 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12696 (cell12696 i)
      scalarRow12696.M scalarRow12696.H scalarRow12696.xi := by
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
    energy_allowance := scalarRow12696.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12696]
    centre_nonneg := (scalarRow12696.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D13.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12696])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12696
/-! Actual 12697 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12697
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12697 ≤ (1.035813488403 : ℝ) := by
  have hr : (112.680965562068 : ℝ) ≤ √(12697 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.680965562068 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12697 12697 (11 / 1000) ≤
    (0.008483127787 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12697) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.680965562068 : ℝ) ≤ √(12697 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12697)
  have hdiv : K / √(12697 : ℝ) ≤ K / 112.680965562068 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.680965562068 ≤ (0.008483127787 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12697.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12697 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12697 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12697 := gPlus_lower 12697
end BstLean.Part269.N12697

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12697
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035813488402 : ℝ) ≤ wn 12697 := by
  have hn : √(12697 : ℝ) ≤ 112.680965562069 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12697 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.680965562069 ≤ 2 / √(12697 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000251941420 : ℝ) ≤ rhoBar 12697 BstLean.Part154.csC ∧
    rhoBar 12697 BstLean.Part154.csC ≤ 0.000251941810 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035813488402 : ℝ) / (1.295212 * 12697) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035813488403 : ℝ) / (1.29521 * 12697) := by gcongr
      _ ≤ (0.000251941810 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12697 BstLean.Part154.csC) ≤ 0.001007830715 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12697 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12697 BstLean.Part154.csC) (piBar (rhoBar 12697 BstLean.Part154.csC)) ≤ 0.000192434856 ∧
    cc1 (rhoBar 12697 BstLean.Part154.csC) (piBar (rhoBar 12697 BstLean.Part154.csC)) ≤ 0.000122447576 ∧
    cc2 (rhoBar 12697 BstLean.Part154.csC) ≤ 0.000071081756 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12697 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12697 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12697 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12697 BstLean.Part154.csC * nuR (rhoBar 12697 BstLean.Part154.csC)) ≤ 0.000503899489 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000251941810 : ℝ) * 0.001007830715 := by gcongr
      _ ≤ (0.000503899489 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12697 BstLean.Part154.csC) * nuR (rhoBar 12697 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001007830715 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12697 BstLean.Part154.csC) * rhoBar 12697 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000251941810 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000251941810 / 2 + 0.399 * 0.001007830715 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000192434856 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000503899489 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122447576 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000251941810 / 1.414213562 := by gcongr
      _ ≤ (0.000071081756 : ℝ) := by norm_num

end BstLean.Part269.N12697

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12697
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12697 BstLean.Part154.csC) (piBar (rhoBar 12697 BstLean.Part154.csC)) ≤ 1.59920E-7 := by
  have hr0 : 0 ≤ rhoBar 12697 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12697 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12697 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12697 BstLean.Part154.csC) (piBar (rhoBar 12697 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12697 BstLean.Part154.csC) (piBar (rhoBar 12697 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12697 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000192434856 : ℝ) ^ 2 + 0.000122447576 ^ 2 + 3 * 0.000071081756 ^ 2 +
        2 * 0.797885 * 0.000192434856 * 0.000122447576 + 2 * 0.000192434856 * 0.000071081756 +
        4 * 0.797885 * 0.000122447576 * 0.000071081756 := by gcongr
    _ ≤ (1.59920E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12697 BstLean.Part154.csC Θ ≤ 0.002629933468 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12697 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12697 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12697 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12697 BstLean.Part154.csC) (piBar (rhoBar 12697 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12697 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035813488403 * 1.59920E-7 / (0.000251941420 : ℝ) := by gcongr
    _ ≤ 0.002629933468 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12697 BstLean.Part154.csC Θ ≤ 0.002918063408 + 0.000664541354 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12697 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12697 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12697 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035813488403 : ℝ) * ((2 * Θ * 0.000251941810 +
        (6863 / 10000) * 0.000251941810 * 12697 * 0.001007830715) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002918063408 + 0.000664541354 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12697 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12697 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12697 0.011 Θ ∧ gammaRatio 12697 0.011 Θ ≤ 0.000086611080 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12697 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035813488403 : ℝ) * 0.525 / ((1 - 0.011) * 12697) := by gcongr
      _ ≤ (0.000086611080 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12697 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12697 0.011 Θ) :=
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
    badAllowance 12697 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000615501984 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12697 BstLean.Part154.csC) 1.22 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 2 (rhoBar 12697 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12697 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12697 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12697 0.011 Θ) 1.12 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 1 (gammaRatio 12697 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12697 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12697 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12697 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12697 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035813488403 : ℝ) * 12697 *
        (2.2721E-8 / 1.1045361 + 2.7751E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000615501984 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12697 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003533565392 + 0.003294474822 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12697

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12697
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12697 BstLean.Part154.csC) (piBar (rhoBar 12697 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12697 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12697 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12697 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12697 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12697 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12697 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12697 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12697 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12697 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12697 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12697 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12697 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12697 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12697 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052490580068 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12697) ≤ 0.010598396767 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12697 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035813488403)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010598396767 + 2 * 0.737676 / 12697) := by gcongr
    _ ≤ (0.052490580068 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12697 12 ≤ 0.0015 := by
  exact BstLean.Part269.S13.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12697

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12697
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560503432590 : ℝ) ≤ plow 12697 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12697) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052769764674)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001380715071) : eMP 12697 0.011 xi bn ≤ 0.001188663098 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12697 : ℝ) * (1 - 0.011))) ≤ 0.000587730580 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001380715071 / (12697 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000587730580 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000587730580 : ℝ) + 3.141593 * 0.052769764674 / (12697 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001188663098 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052769764674)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001380715071) : PiBarMP 12697 12 0.011 xi bn ≤ 0.161270298499 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12697 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037157974528 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.059506513280 : ℝ) ≤ √((12697 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.680965562068 : ℝ) ≤ √(12697 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12697) ≤ 0.123644736210 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037157974528 + 0.052769764674 * 1.772454 / (2 * (112.059506513280 : ℝ))) * (1 + 0.001188663098) +
        8 / (12697 * 112.680965562068) + 0.123644736210 := by gcongr
    _ ≤ (0.161270298499 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052769764674)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001380715071) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282207285325) :
    parallelOracle 12697 0.011 xi bn cd ≤ 0.162261087238 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12697 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12697 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560503432590 : ℝ) ≤ plow 12697 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.680965562068 : ℝ) ≤ √(12697 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282207285325 : ℝ) / (2 * 0.560503432590 * 112.680965562068)) * 0.161270298499 +
        0.282207285325 ^ 2 / (2 * 0.560503432590 * 112.680965562068) := by gcongr
    _ ≤ (0.162261087238 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052769764674) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001380715071)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282207285325) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12697 12697 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560503432590 : ℝ) ≤ plow 12697 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.680965562068 : ℝ) ≤ √(12697 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12697 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12697 Θ 1.22 ≤ 0.011768629186 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.680965562068 := by gcongr <;> linarith
      _ ≤ (0.011768629186 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12697 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12697 12697 0.011 ≤ 0.008483127787 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12697 12697 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12697 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12697 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12697 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12697 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162261087238 + 0.011768629186 + (0.008483127787 : ℝ) *
        (1 + 2 * (0.282207285325 + 0.011768629186) / (0.560503432590 * 112.680965562068))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12697]

end BstLean.Part269.N12697

/-! The original eight local profiles supply actual 12697 moment certificates. -/
namespace BstLean.Part269.N12697
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12697 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12697 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12697 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052769764674 ∧
    0 ≤ bN 12697 BstLean.Part154.csC (groupTheta g) ∧ bN 12697 BstLean.Part154.csC (groupTheta g) ≤ 0.001380715071 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12697 12697 0.011
      (momentAllowance 12697 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12697 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12697 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12697 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12697 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12697 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229716705257 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12697 0.011
      (momentAllowance 12697 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12697 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12697
/-! The actual computed-centre upper energy formula at 12697. -/
namespace BstLean.Part269.N12697
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12697

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12697
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12697)
open BstLean.Part268 (cell12697)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085499009978
  | 2 => 0.086441920178
  | 3 => 0.087382993504
  | 4 => 0.088323653426
  | 5 => 0.089265621534
  | 6 => 0.090210961791
  | 7 => 0.091162128949
  | 8 => 0.092122021167
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12697 12697 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12697 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003538895953 + 0.003300387184 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S13.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12697

/-! Actual upper energy certificates on all 43 source endpoints at 12697. -/
namespace BstLean.Part269.N12697
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12697)
open BstLean.Part268 (cell12697)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12697 (gMinus 12697) (1 - (cell12697 i).lower) ≤ 1 ∧
    energyUpper 12697 (gMinus 12697) (BstLean.Part211.gPlus 12697)
      (finiteEnergy 12697 12697 0.011) (1 - (cell12697 i).lower) ≤
      (cell12697 i).energy := by
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
      have E := BstLean.Part269.S13.uniformEnergy10 (n := 12697) (by norm_num)
        (q := 1 - (cell12697 ⟨10,by decide⟩).lower)
        (by norm_num [cell12697]) (by norm_num [cell12697])
      exact ⟨E.1,E.2.trans (by norm_num [cell12697])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy11 (n := 12697) (by norm_num)
        (q := 1 - (cell12697 ⟨11,by decide⟩).lower)
        (by norm_num [cell12697]) (by norm_num [cell12697])
      exact ⟨E.1,E.2.trans (by norm_num [cell12697])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy12 (n := 12697) (by norm_num)
        (q := 1 - (cell12697 ⟨12,by decide⟩).lower)
        (by norm_num [cell12697]) (by norm_num [cell12697])
      exact ⟨E.1,E.2.trans (by norm_num [cell12697])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy13 (n := 12697) (by norm_num)
        (q := 1 - (cell12697 ⟨13,by decide⟩).lower)
        (by norm_num [cell12697]) (by norm_num [cell12697])
      exact ⟨E.1,E.2.trans (by norm_num [cell12697])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy14 (n := 12697) (by norm_num)
        (q := 1 - (cell12697 ⟨14,by decide⟩).lower)
        (by norm_num [cell12697]) (by norm_num [cell12697])
      exact ⟨E.1,E.2.trans (by norm_num [cell12697])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy15 (n := 12697) (by norm_num)
        (q := 1 - (cell12697 ⟨15,by decide⟩).lower)
        (by norm_num [cell12697]) (by norm_num [cell12697])
      exact ⟨E.1,E.2.trans (by norm_num [cell12697])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy16 (n := 12697) (by norm_num)
        (q := 1 - (cell12697 ⟨16,by decide⟩).lower)
        (by norm_num [cell12697]) (by norm_num [cell12697])
      exact ⟨E.1,E.2.trans (by norm_num [cell12697])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy17 (n := 12697) (by norm_num)
        (q := 1 - (cell12697 ⟨17,by decide⟩).lower)
        (by norm_num [cell12697]) (by norm_num [cell12697])
      exact ⟨E.1,E.2.trans (by norm_num [cell12697])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy18 (n := 12697) (by norm_num)
        (q := 1 - (cell12697 ⟨18,by decide⟩).lower)
        (by norm_num [cell12697]) (by norm_num [cell12697])
      exact ⟨E.1,E.2.trans (by norm_num [cell12697])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy19 (n := 12697) (by norm_num)
        (q := 1 - (cell12697 ⟨19,by decide⟩).lower)
        (by norm_num [cell12697]) (by norm_num [cell12697])
      exact ⟨E.1,E.2.trans (by norm_num [cell12697])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy20 (n := 12697) (by norm_num)
        (q := 1 - (cell12697 ⟨20,by decide⟩).lower)
        (by norm_num [cell12697]) (by norm_num [cell12697])
      exact ⟨E.1,E.2.trans (by norm_num [cell12697])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy21 (n := 12697) (by norm_num)
        (q := 1 - (cell12697 ⟨21,by decide⟩).lower)
        (by norm_num [cell12697]) (by norm_num [cell12697])
      exact ⟨E.1,E.2.trans (by norm_num [cell12697])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy22 (n := 12697) (by norm_num)
        (q := 1 - (cell12697 ⟨22,by decide⟩).lower)
        (by norm_num [cell12697]) (by norm_num [cell12697])
      exact ⟨E.1,E.2.trans (by norm_num [cell12697])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy23 (n := 12697) (by norm_num)
        (q := 1 - (cell12697 ⟨23,by decide⟩).lower)
        (by norm_num [cell12697]) (by norm_num [cell12697])
      exact ⟨E.1,E.2.trans (by norm_num [cell12697])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy24 (n := 12697) (by norm_num)
        (q := 1 - (cell12697 ⟨24,by decide⟩).lower)
        (by norm_num [cell12697]) (by norm_num [cell12697])
      exact ⟨E.1,E.2.trans (by norm_num [cell12697])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy25 (n := 12697) (by norm_num)
        (q := 1 - (cell12697 ⟨25,by decide⟩).lower)
        (by norm_num [cell12697]) (by norm_num [cell12697])
      exact ⟨E.1,E.2.trans (by norm_num [cell12697])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy26 (n := 12697) (by norm_num)
        (q := 1 - (cell12697 ⟨26,by decide⟩).lower)
        (by norm_num [cell12697]) (by norm_num [cell12697])
      exact ⟨E.1,E.2.trans (by norm_num [cell12697])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy27 (n := 12697) (by norm_num)
        (q := 1 - (cell12697 ⟨27,by decide⟩).lower)
        (by norm_num [cell12697]) (by norm_num [cell12697])
      exact ⟨E.1,E.2.trans (by norm_num [cell12697])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy28 (n := 12697) (by norm_num)
        (q := 1 - (cell12697 ⟨28,by decide⟩).lower)
        (by norm_num [cell12697]) (by norm_num [cell12697])
      exact ⟨E.1,E.2.trans (by norm_num [cell12697])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy29 (n := 12697) (by norm_num)
        (q := 1 - (cell12697 ⟨29,by decide⟩).lower)
        (by norm_num [cell12697]) (by norm_num [cell12697])
      exact ⟨E.1,E.2.trans (by norm_num [cell12697])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy30 (n := 12697) (by norm_num)
        (q := 1 - (cell12697 ⟨30,by decide⟩).lower)
        (by norm_num [cell12697]) (by norm_num [cell12697])
      exact ⟨E.1,E.2.trans (by norm_num [cell12697])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy31 (n := 12697) (by norm_num)
        (q := 1 - (cell12697 ⟨31,by decide⟩).lower)
        (by norm_num [cell12697]) (by norm_num [cell12697])
      exact ⟨E.1,E.2.trans (by norm_num [cell12697])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy32 (n := 12697) (by norm_num)
        (q := 1 - (cell12697 ⟨32,by decide⟩).lower)
        (by norm_num [cell12697]) (by norm_num [cell12697])
      exact ⟨E.1,E.2.trans (by norm_num [cell12697])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy33 (n := 12697) (by norm_num)
        (q := 1 - (cell12697 ⟨33,by decide⟩).lower)
        (by norm_num [cell12697]) (by norm_num [cell12697])
      exact ⟨E.1,E.2.trans (by norm_num [cell12697])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy34 (n := 12697) (by norm_num)
        (q := 1 - (cell12697 ⟨34,by decide⟩).lower)
        (by norm_num [cell12697]) (by norm_num [cell12697])
      exact ⟨E.1,E.2.trans (by norm_num [cell12697])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy35 (n := 12697) (by norm_num)
        (q := 1 - (cell12697 ⟨35,by decide⟩).lower)
        (by norm_num [cell12697]) (by norm_num [cell12697])
      exact ⟨E.1,E.2.trans (by norm_num [cell12697])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy36 (n := 12697) (by norm_num)
        (q := 1 - (cell12697 ⟨36,by decide⟩).lower)
        (by norm_num [cell12697]) (by norm_num [cell12697])
      exact ⟨E.1,E.2.trans (by norm_num [cell12697])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy37 (n := 12697) (by norm_num)
        (q := 1 - (cell12697 ⟨37,by decide⟩).lower)
        (by norm_num [cell12697]) (by norm_num [cell12697])
      exact ⟨E.1,E.2.trans (by norm_num [cell12697])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy38 (n := 12697) (by norm_num)
        (q := 1 - (cell12697 ⟨38,by decide⟩).lower)
        (by norm_num [cell12697]) (by norm_num [cell12697])
      exact ⟨E.1,E.2.trans (by norm_num [cell12697])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy39 (n := 12697) (by norm_num)
        (q := 1 - (cell12697 ⟨39,by decide⟩).lower)
        (by norm_num [cell12697]) (by norm_num [cell12697])
      exact ⟨E.1,E.2.trans (by norm_num [cell12697])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy40 (n := 12697) (by norm_num)
        (q := 1 - (cell12697 ⟨40,by decide⟩).lower)
        (by norm_num [cell12697]) (by norm_num [cell12697])
      exact ⟨E.1,E.2.trans (by norm_num [cell12697])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy41 (n := 12697) (by norm_num)
        (q := 1 - (cell12697 ⟨41,by decide⟩).lower)
        (by norm_num [cell12697]) (by norm_num [cell12697])
      exact ⟨E.1,E.2.trans (by norm_num [cell12697])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy42 (n := 12697) (by norm_num)
        (q := 1 - (cell12697 ⟨42,by decide⟩).lower)
        (by norm_num [cell12697]) (by norm_num [cell12697])
      exact ⟨E.1,E.2.trans (by norm_num [cell12697])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy43 (n := 12697) (by norm_num)
        (q := 1 - (cell12697 ⟨43,by decide⟩).lower)
        (by norm_num [cell12697]) (by norm_num [cell12697])
      exact ⟨E.1,E.2.trans (by norm_num [cell12697])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy44 (n := 12697) (by norm_num)
        (q := 1 - (cell12697 ⟨44,by decide⟩).lower)
        (by norm_num [cell12697]) (by norm_num [cell12697])
      exact ⟨E.1,E.2.trans (by norm_num [cell12697])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy45 (n := 12697) (by norm_num)
        (q := 1 - (cell12697 ⟨45,by decide⟩).lower)
        (by norm_num [cell12697]) (by norm_num [cell12697])
      exact ⟨E.1,E.2.trans (by norm_num [cell12697])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy46 (n := 12697) (by norm_num)
        (q := 1 - (cell12697 ⟨46,by decide⟩).lower)
        (by norm_num [cell12697]) (by norm_num [cell12697])
      exact ⟨E.1,E.2.trans (by norm_num [cell12697])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy47 (n := 12697) (by norm_num)
        (q := 1 - (cell12697 ⟨47,by decide⟩).lower)
        (by norm_num [cell12697]) (by norm_num [cell12697])
      exact ⟨E.1,E.2.trans (by norm_num [cell12697])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy48 (n := 12697) (by norm_num)
        (q := 1 - (cell12697 ⟨48,by decide⟩).lower)
        (by norm_num [cell12697]) (by norm_num [cell12697])
      exact ⟨E.1,E.2.trans (by norm_num [cell12697])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy49 (n := 12697) (by norm_num)
        (q := 1 - (cell12697 ⟨49,by decide⟩).lower)
        (by norm_num [cell12697]) (by norm_num [cell12697])
      exact ⟨E.1,E.2.trans (by norm_num [cell12697])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy50 (n := 12697) (by norm_num)
        (q := 1 - (cell12697 ⟨50,by decide⟩).lower)
        (by norm_num [cell12697]) (by norm_num [cell12697])
      exact ⟨E.1,E.2.trans (by norm_num [cell12697])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy51 (n := 12697) (by norm_num)
        (q := 1 - (cell12697 ⟨51,by decide⟩).lower)
        (by norm_num [cell12697]) (by norm_num [cell12697])
      exact ⟨E.1,E.2.trans (by norm_num [cell12697])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy52 (n := 12697) (by norm_num)
        (q := 1 - (cell12697 ⟨52,by decide⟩).lower)
        (by norm_num [cell12697]) (by norm_num [cell12697])
      exact ⟨E.1,E.2.trans (by norm_num [cell12697])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12697

/-! Source-cell containment and simple scalar guards at 12697. -/
namespace BstLean.Part269.N12697
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12697)
open BstLean.Part268 (cell12697)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12697 ⟨10,by decide⟩).lower ∧ (cell12697 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12697 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12697 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12697 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12697 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12697 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12697,cell12697,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12697 ⟨11,by decide⟩).lower ∧ (cell12697 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12697 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12697 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12697 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12697 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12697 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12697,cell12697,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12697 ⟨12,by decide⟩).lower ∧ (cell12697 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12697 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12697 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12697 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12697 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12697 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12697,cell12697,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12697 ⟨13,by decide⟩).lower ∧ (cell12697 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12697 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12697 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12697 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12697 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12697 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12697,cell12697,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12697 ⟨14,by decide⟩).lower ∧ (cell12697 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12697 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12697 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12697 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12697 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12697 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12697,cell12697,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12697 ⟨15,by decide⟩).lower ∧ (cell12697 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12697 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12697 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12697 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12697 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12697 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12697,cell12697,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12697 ⟨16,by decide⟩).lower ∧ (cell12697 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12697 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12697 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12697 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12697 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12697 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12697,cell12697,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12697 ⟨17,by decide⟩).lower ∧ (cell12697 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12697 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12697 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12697 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12697 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12697 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12697,cell12697,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12697 ⟨18,by decide⟩).lower ∧ (cell12697 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12697 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12697 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12697 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12697 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12697 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12697,cell12697,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12697 ⟨19,by decide⟩).lower ∧ (cell12697 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12697 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12697 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12697 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12697 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12697 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12697,cell12697,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12697 ⟨20,by decide⟩).lower ∧ (cell12697 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12697 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12697 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12697 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12697 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12697 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12697,cell12697,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12697 ⟨21,by decide⟩).lower ∧ (cell12697 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12697 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12697 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12697 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12697 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12697 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12697,cell12697,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12697 ⟨22,by decide⟩).lower ∧ (cell12697 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12697 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12697 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12697 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12697 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12697 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12697,cell12697,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12697 ⟨23,by decide⟩).lower ∧ (cell12697 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12697 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12697 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12697 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12697 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12697 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12697,cell12697,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12697 ⟨24,by decide⟩).lower ∧ (cell12697 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12697 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12697 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12697 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12697 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12697 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12697,cell12697,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12697 ⟨25,by decide⟩).lower ∧ (cell12697 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12697 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12697 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12697 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12697 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12697 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12697,cell12697,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12697 ⟨26,by decide⟩).lower ∧ (cell12697 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12697 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12697 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12697 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12697 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12697 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12697,cell12697,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12697 ⟨27,by decide⟩).lower ∧ (cell12697 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12697 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12697 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12697 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12697 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12697 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12697,cell12697,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12697 ⟨28,by decide⟩).lower ∧ (cell12697 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12697 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12697 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12697 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12697 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12697 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12697,cell12697,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12697 ⟨29,by decide⟩).lower ∧ (cell12697 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12697 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12697 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12697 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12697 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12697 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12697,cell12697,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12697 ⟨30,by decide⟩).lower ∧ (cell12697 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12697 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12697 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12697 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12697 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12697 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12697,cell12697,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12697 ⟨31,by decide⟩).lower ∧ (cell12697 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12697 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12697 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12697 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12697 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12697 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12697,cell12697,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12697 ⟨32,by decide⟩).lower ∧ (cell12697 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12697 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12697 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12697 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12697 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12697 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12697,cell12697,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12697 ⟨33,by decide⟩).lower ∧ (cell12697 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12697 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12697 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12697 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12697 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12697 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12697,cell12697,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12697 ⟨34,by decide⟩).lower ∧ (cell12697 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12697 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12697 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12697 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12697 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12697 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12697,cell12697,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12697 ⟨35,by decide⟩).lower ∧ (cell12697 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12697 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12697 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12697 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12697 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12697 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12697,cell12697,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12697 ⟨36,by decide⟩).lower ∧ (cell12697 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12697 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12697 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12697 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12697 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12697 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12697,cell12697,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12697 ⟨37,by decide⟩).lower ∧ (cell12697 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12697 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12697 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12697 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12697 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12697 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12697,cell12697,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12697 ⟨38,by decide⟩).lower ∧ (cell12697 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12697 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12697 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12697 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12697 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12697 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12697,cell12697,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12697 ⟨39,by decide⟩).lower ∧ (cell12697 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12697 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12697 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12697 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12697 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12697 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12697,cell12697,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12697 ⟨40,by decide⟩).lower ∧ (cell12697 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12697 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12697 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12697 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12697 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12697 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12697,cell12697,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12697 ⟨41,by decide⟩).lower ∧ (cell12697 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12697 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12697 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12697 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12697 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12697 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12697,cell12697,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12697 ⟨42,by decide⟩).lower ∧ (cell12697 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12697 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12697 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12697 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12697 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12697 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12697,cell12697,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12697 ⟨43,by decide⟩).lower ∧ (cell12697 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12697 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12697 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12697 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12697 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12697 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12697,cell12697,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12697 ⟨44,by decide⟩).lower ∧ (cell12697 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12697 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12697 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12697 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12697 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12697 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12697,cell12697,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12697 ⟨45,by decide⟩).lower ∧ (cell12697 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12697 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12697 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12697 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12697 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12697 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12697,cell12697,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12697 ⟨46,by decide⟩).lower ∧ (cell12697 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12697 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12697 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12697 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12697 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12697 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12697,cell12697,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12697 ⟨47,by decide⟩).lower ∧ (cell12697 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12697 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12697 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12697 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12697 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12697 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12697,cell12697,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12697 ⟨48,by decide⟩).lower ∧ (cell12697 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12697 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12697 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12697 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12697 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12697 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12697,cell12697,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12697 ⟨49,by decide⟩).lower ∧ (cell12697 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12697 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12697 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12697 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12697 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12697 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12697,cell12697,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12697 ⟨50,by decide⟩).lower ∧ (cell12697 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12697 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12697 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12697 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12697 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12697 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12697,cell12697,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12697 ⟨51,by decide⟩).lower ∧ (cell12697 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12697 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12697 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12697 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12697 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12697 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12697,cell12697,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12697 ⟨52,by decide⟩).lower ∧ (cell12697 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12697 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12697 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12697 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12697 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12697 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12697,cell12697,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12697 i).lower ∧
    (cell12697 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12697 i).upper ≤ (0.532 : ℝ) ∧
    (cell12697 i).centre ≤ (0.1 : ℝ) ∧ (cell12697 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12697 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12697 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12697

/-! The local source numeric instances at 12697 have no network premises. -/
namespace BstLean.Part269.N12697
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12697)
open BstLean.Part268 (cell12697)

noncomputable def sourceNumerics12697 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12697 (cell12697 i)
      scalarRow12697.M scalarRow12697.H scalarRow12697.xi := by
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
    energy_allowance := scalarRow12697.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12697]
    centre_nonneg := (scalarRow12697.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D13.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12697])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12697
/-! Actual 12698 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12698
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12698 ≤ (1.035812065769 : ℝ) := by
  have hr : (112.685402781371 : ℝ) ≤ √(12698 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.685402781371 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12698 12698 (11 / 1000) ≤
    (0.008482793744 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12698) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.685402781371 : ℝ) ≤ √(12698 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12698)
  have hdiv : K / √(12698 : ℝ) ≤ K / 112.685402781371 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.685402781371 ≤ (0.008482793744 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12698.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12698 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12698 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12698 := gPlus_lower 12698
end BstLean.Part269.N12698

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12698
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035812065768 : ℝ) ≤ wn 12698 := by
  have hn : √(12698 : ℝ) ≤ 112.685402781372 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12698 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.685402781372 ≤ 2 / √(12698 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000251921233 : ℝ) ≤ rhoBar 12698 BstLean.Part154.csC ∧
    rhoBar 12698 BstLean.Part154.csC ≤ 0.000251921623 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035812065768 : ℝ) / (1.295212 * 12698) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035812065769 : ℝ) / (1.29521 * 12698) := by gcongr
      _ ≤ (0.000251921623 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12698 BstLean.Part154.csC) ≤ 0.001007749957 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12698 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12698 BstLean.Part154.csC) (piBar (rhoBar 12698 BstLean.Part154.csC)) ≤ 0.000192419437 ∧
    cc1 (rhoBar 12698 BstLean.Part154.csC) (piBar (rhoBar 12698 BstLean.Part154.csC)) ≤ 0.000122437765 ∧
    cc2 (rhoBar 12698 BstLean.Part154.csC) ≤ 0.000071076060 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12698 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12698 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12698 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12698 BstLean.Part154.csC * nuR (rhoBar 12698 BstLean.Part154.csC)) ≤ 0.000503859113 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000251921623 : ℝ) * 0.001007749957 := by gcongr
      _ ≤ (0.000503859113 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12698 BstLean.Part154.csC) * nuR (rhoBar 12698 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001007749957 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12698 BstLean.Part154.csC) * rhoBar 12698 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000251921623 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000251921623 / 2 + 0.399 * 0.001007749957 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000192419437 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000503859113 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122437765 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000251921623 / 1.414213562 := by gcongr
      _ ≤ (0.000071076060 : ℝ) := by norm_num

end BstLean.Part269.N12698

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12698
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12698 BstLean.Part154.csC) (piBar (rhoBar 12698 BstLean.Part154.csC)) ≤ 1.59894E-7 := by
  have hr0 : 0 ≤ rhoBar 12698 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12698 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12698 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12698 BstLean.Part154.csC) (piBar (rhoBar 12698 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12698 BstLean.Part154.csC) (piBar (rhoBar 12698 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12698 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000192419437 : ℝ) ^ 2 + 0.000122437765 ^ 2 + 3 * 0.000071076060 ^ 2 +
        2 * 0.797885 * 0.000192419437 * 0.000122437765 + 2 * 0.000192419437 * 0.000071076060 +
        4 * 0.797885 * 0.000122437765 * 0.000071076060 := by gcongr
    _ ≤ (1.59894E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12698 BstLean.Part154.csC Θ ≤ 0.002629712986 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12698 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12698 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12698 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12698 BstLean.Part154.csC) (piBar (rhoBar 12698 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12698 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035812065769 * 1.59894E-7 / (0.000251921233 : ℝ) := by gcongr
    _ ≤ 0.002629712986 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12698 BstLean.Part154.csC Θ ≤ 0.002917821568 + 0.000664487195 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12698 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12698 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12698 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035812065769 : ℝ) * ((2 * Θ * 0.000251921623 +
        (6863 / 10000) * 0.000251921623 * 12698 * 0.001007749957) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002917821568 + 0.000664487195 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12698 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12698 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12698 0.011 Θ ∧ gammaRatio 12698 0.011 Θ ≤ 0.000086604140 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12698 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035812065769 : ℝ) * 0.525 / ((1 - 0.011) * 12698) := by gcongr
      _ ≤ (0.000086604140 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12698 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12698 0.011 Θ) :=
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
    badAllowance 12698 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000615501984 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12698 BstLean.Part154.csC) 1.22 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 2 (rhoBar 12698 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12698 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12698 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12698 0.011 Θ) 1.12 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 1 (gammaRatio 12698 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12698 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12698 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12698 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12698 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035812065769 : ℝ) * 12698 *
        (2.2721E-8 / 1.1045361 + 2.7751E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000615501984 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12698 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003533323552 + 0.003294200181 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12698

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12698
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12698 BstLean.Part154.csC) (piBar (rhoBar 12698 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12698 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12698 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12698 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12698 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12698 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12698 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12698 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12698 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12698 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12698 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12698 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12698 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12698 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12698 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052488490728 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12698) ≤ 0.010597979433 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12698 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035812065769)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010597979433 + 2 * 0.737676 / 12698) := by gcongr
    _ ≤ (0.052488490728 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12698 12 ≤ 0.0015 := by
  exact BstLean.Part269.S13.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12698

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12698
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560503477831 : ℝ) ≤ plow 12698 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12698) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052769378648)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001380599318) : eMP 12698 0.011 xi bn ≤ 0.001188566404 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12698 : ℝ) * (1 - 0.011))) ≤ 0.000587682801 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001380599318 / (12698 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000587682801 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000587682801 : ℝ) + 3.141593 * 0.052769378648 / (12698 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001188566404 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052769378648)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001380599318) : PiBarMP 12698 12 0.011 xi bn ≤ 0.161263846467 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12698 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037156416916 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.063919260393 : ℝ) ≤ √((12698 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.685402781371 : ℝ) ≤ √(12698 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12698) ≤ 0.123639867444 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037156416916 + 0.052769378648 * 1.772454 / (2 * (112.063919260393 : ℝ))) * (1 + 0.001188566404) +
        8 / (12698 * 112.685402781371) + 0.123639867444 := by gcongr
    _ ≤ (0.161263846467 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052769378648)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001380599318) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282204355762) :
    parallelOracle 12698 0.011 xi bn cd ≤ 0.162254564868 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12698 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12698 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560503477831 : ℝ) ≤ plow 12698 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.685402781371 : ℝ) ≤ √(12698 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282204355762 : ℝ) / (2 * 0.560503477831 * 112.685402781371)) * 0.161263846467 +
        0.282204355762 ^ 2 / (2 * 0.560503477831 * 112.685402781371) := by gcongr
    _ ≤ (0.162254564868 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052769378648) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001380599318)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282204355762) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12698 12698 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560503477831 : ℝ) ≤ plow 12698 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.685402781371 : ℝ) ≤ √(12698 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12698 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12698 Θ 1.22 ≤ 0.011768165772 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.685402781371 := by gcongr <;> linarith
      _ ≤ (0.011768165772 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12698 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12698 12698 0.011 ≤ 0.008482793744 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12698 12698 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12698 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12698 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12698 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12698 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162254564868 + 0.011768165772 + (0.008482793744 : ℝ) *
        (1 + 2 * (0.282204355762 + 0.011768165772) / (0.560503477831 * 112.685402781371))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12698]

end BstLean.Part269.N12698

/-! The original eight local profiles supply actual 12698 moment certificates. -/
namespace BstLean.Part269.N12698
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12698 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12698 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12698 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052769378648 ∧
    0 ≤ bN 12698 BstLean.Part154.csC (groupTheta g) ∧ bN 12698 BstLean.Part154.csC (groupTheta g) ≤ 0.001380599318 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12698 12698 0.011
      (momentAllowance 12698 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12698 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12698 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12698 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12698 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12698 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229715865034 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12698 0.011
      (momentAllowance 12698 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12698 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12698
/-! The actual computed-centre upper energy formula at 12698. -/
namespace BstLean.Part269.N12698
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12698

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12698
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12698)
open BstLean.Part268 (cell12698)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085496090970
  | 2 => 0.086438947481
  | 3 => 0.087379959274
  | 4 => 0.088320548015
  | 5 => 0.089262433170
  | 6 => 0.090207676218
  | 7 => 0.091158729027
  | 8 => 0.092118486431
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12698 12698 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12698 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003538895953 + 0.003300387184 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S13.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12698

/-! Actual upper energy certificates on all 43 source endpoints at 12698. -/
namespace BstLean.Part269.N12698
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12698)
open BstLean.Part268 (cell12698)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12698 (gMinus 12698) (1 - (cell12698 i).lower) ≤ 1 ∧
    energyUpper 12698 (gMinus 12698) (BstLean.Part211.gPlus 12698)
      (finiteEnergy 12698 12698 0.011) (1 - (cell12698 i).lower) ≤
      (cell12698 i).energy := by
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
      have E := BstLean.Part269.S13.uniformEnergy10 (n := 12698) (by norm_num)
        (q := 1 - (cell12698 ⟨10,by decide⟩).lower)
        (by norm_num [cell12698]) (by norm_num [cell12698])
      exact ⟨E.1,E.2.trans (by norm_num [cell12698])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy11 (n := 12698) (by norm_num)
        (q := 1 - (cell12698 ⟨11,by decide⟩).lower)
        (by norm_num [cell12698]) (by norm_num [cell12698])
      exact ⟨E.1,E.2.trans (by norm_num [cell12698])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy12 (n := 12698) (by norm_num)
        (q := 1 - (cell12698 ⟨12,by decide⟩).lower)
        (by norm_num [cell12698]) (by norm_num [cell12698])
      exact ⟨E.1,E.2.trans (by norm_num [cell12698])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy13 (n := 12698) (by norm_num)
        (q := 1 - (cell12698 ⟨13,by decide⟩).lower)
        (by norm_num [cell12698]) (by norm_num [cell12698])
      exact ⟨E.1,E.2.trans (by norm_num [cell12698])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy14 (n := 12698) (by norm_num)
        (q := 1 - (cell12698 ⟨14,by decide⟩).lower)
        (by norm_num [cell12698]) (by norm_num [cell12698])
      exact ⟨E.1,E.2.trans (by norm_num [cell12698])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy15 (n := 12698) (by norm_num)
        (q := 1 - (cell12698 ⟨15,by decide⟩).lower)
        (by norm_num [cell12698]) (by norm_num [cell12698])
      exact ⟨E.1,E.2.trans (by norm_num [cell12698])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy16 (n := 12698) (by norm_num)
        (q := 1 - (cell12698 ⟨16,by decide⟩).lower)
        (by norm_num [cell12698]) (by norm_num [cell12698])
      exact ⟨E.1,E.2.trans (by norm_num [cell12698])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy17 (n := 12698) (by norm_num)
        (q := 1 - (cell12698 ⟨17,by decide⟩).lower)
        (by norm_num [cell12698]) (by norm_num [cell12698])
      exact ⟨E.1,E.2.trans (by norm_num [cell12698])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy18 (n := 12698) (by norm_num)
        (q := 1 - (cell12698 ⟨18,by decide⟩).lower)
        (by norm_num [cell12698]) (by norm_num [cell12698])
      exact ⟨E.1,E.2.trans (by norm_num [cell12698])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy19 (n := 12698) (by norm_num)
        (q := 1 - (cell12698 ⟨19,by decide⟩).lower)
        (by norm_num [cell12698]) (by norm_num [cell12698])
      exact ⟨E.1,E.2.trans (by norm_num [cell12698])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy20 (n := 12698) (by norm_num)
        (q := 1 - (cell12698 ⟨20,by decide⟩).lower)
        (by norm_num [cell12698]) (by norm_num [cell12698])
      exact ⟨E.1,E.2.trans (by norm_num [cell12698])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy21 (n := 12698) (by norm_num)
        (q := 1 - (cell12698 ⟨21,by decide⟩).lower)
        (by norm_num [cell12698]) (by norm_num [cell12698])
      exact ⟨E.1,E.2.trans (by norm_num [cell12698])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy22 (n := 12698) (by norm_num)
        (q := 1 - (cell12698 ⟨22,by decide⟩).lower)
        (by norm_num [cell12698]) (by norm_num [cell12698])
      exact ⟨E.1,E.2.trans (by norm_num [cell12698])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy23 (n := 12698) (by norm_num)
        (q := 1 - (cell12698 ⟨23,by decide⟩).lower)
        (by norm_num [cell12698]) (by norm_num [cell12698])
      exact ⟨E.1,E.2.trans (by norm_num [cell12698])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy24 (n := 12698) (by norm_num)
        (q := 1 - (cell12698 ⟨24,by decide⟩).lower)
        (by norm_num [cell12698]) (by norm_num [cell12698])
      exact ⟨E.1,E.2.trans (by norm_num [cell12698])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy25 (n := 12698) (by norm_num)
        (q := 1 - (cell12698 ⟨25,by decide⟩).lower)
        (by norm_num [cell12698]) (by norm_num [cell12698])
      exact ⟨E.1,E.2.trans (by norm_num [cell12698])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy26 (n := 12698) (by norm_num)
        (q := 1 - (cell12698 ⟨26,by decide⟩).lower)
        (by norm_num [cell12698]) (by norm_num [cell12698])
      exact ⟨E.1,E.2.trans (by norm_num [cell12698])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy27 (n := 12698) (by norm_num)
        (q := 1 - (cell12698 ⟨27,by decide⟩).lower)
        (by norm_num [cell12698]) (by norm_num [cell12698])
      exact ⟨E.1,E.2.trans (by norm_num [cell12698])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy28 (n := 12698) (by norm_num)
        (q := 1 - (cell12698 ⟨28,by decide⟩).lower)
        (by norm_num [cell12698]) (by norm_num [cell12698])
      exact ⟨E.1,E.2.trans (by norm_num [cell12698])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy29 (n := 12698) (by norm_num)
        (q := 1 - (cell12698 ⟨29,by decide⟩).lower)
        (by norm_num [cell12698]) (by norm_num [cell12698])
      exact ⟨E.1,E.2.trans (by norm_num [cell12698])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy30 (n := 12698) (by norm_num)
        (q := 1 - (cell12698 ⟨30,by decide⟩).lower)
        (by norm_num [cell12698]) (by norm_num [cell12698])
      exact ⟨E.1,E.2.trans (by norm_num [cell12698])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy31 (n := 12698) (by norm_num)
        (q := 1 - (cell12698 ⟨31,by decide⟩).lower)
        (by norm_num [cell12698]) (by norm_num [cell12698])
      exact ⟨E.1,E.2.trans (by norm_num [cell12698])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy32 (n := 12698) (by norm_num)
        (q := 1 - (cell12698 ⟨32,by decide⟩).lower)
        (by norm_num [cell12698]) (by norm_num [cell12698])
      exact ⟨E.1,E.2.trans (by norm_num [cell12698])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy33 (n := 12698) (by norm_num)
        (q := 1 - (cell12698 ⟨33,by decide⟩).lower)
        (by norm_num [cell12698]) (by norm_num [cell12698])
      exact ⟨E.1,E.2.trans (by norm_num [cell12698])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy34 (n := 12698) (by norm_num)
        (q := 1 - (cell12698 ⟨34,by decide⟩).lower)
        (by norm_num [cell12698]) (by norm_num [cell12698])
      exact ⟨E.1,E.2.trans (by norm_num [cell12698])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy35 (n := 12698) (by norm_num)
        (q := 1 - (cell12698 ⟨35,by decide⟩).lower)
        (by norm_num [cell12698]) (by norm_num [cell12698])
      exact ⟨E.1,E.2.trans (by norm_num [cell12698])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy36 (n := 12698) (by norm_num)
        (q := 1 - (cell12698 ⟨36,by decide⟩).lower)
        (by norm_num [cell12698]) (by norm_num [cell12698])
      exact ⟨E.1,E.2.trans (by norm_num [cell12698])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy37 (n := 12698) (by norm_num)
        (q := 1 - (cell12698 ⟨37,by decide⟩).lower)
        (by norm_num [cell12698]) (by norm_num [cell12698])
      exact ⟨E.1,E.2.trans (by norm_num [cell12698])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy38 (n := 12698) (by norm_num)
        (q := 1 - (cell12698 ⟨38,by decide⟩).lower)
        (by norm_num [cell12698]) (by norm_num [cell12698])
      exact ⟨E.1,E.2.trans (by norm_num [cell12698])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy39 (n := 12698) (by norm_num)
        (q := 1 - (cell12698 ⟨39,by decide⟩).lower)
        (by norm_num [cell12698]) (by norm_num [cell12698])
      exact ⟨E.1,E.2.trans (by norm_num [cell12698])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy40 (n := 12698) (by norm_num)
        (q := 1 - (cell12698 ⟨40,by decide⟩).lower)
        (by norm_num [cell12698]) (by norm_num [cell12698])
      exact ⟨E.1,E.2.trans (by norm_num [cell12698])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy41 (n := 12698) (by norm_num)
        (q := 1 - (cell12698 ⟨41,by decide⟩).lower)
        (by norm_num [cell12698]) (by norm_num [cell12698])
      exact ⟨E.1,E.2.trans (by norm_num [cell12698])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy42 (n := 12698) (by norm_num)
        (q := 1 - (cell12698 ⟨42,by decide⟩).lower)
        (by norm_num [cell12698]) (by norm_num [cell12698])
      exact ⟨E.1,E.2.trans (by norm_num [cell12698])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy43 (n := 12698) (by norm_num)
        (q := 1 - (cell12698 ⟨43,by decide⟩).lower)
        (by norm_num [cell12698]) (by norm_num [cell12698])
      exact ⟨E.1,E.2.trans (by norm_num [cell12698])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy44 (n := 12698) (by norm_num)
        (q := 1 - (cell12698 ⟨44,by decide⟩).lower)
        (by norm_num [cell12698]) (by norm_num [cell12698])
      exact ⟨E.1,E.2.trans (by norm_num [cell12698])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy45 (n := 12698) (by norm_num)
        (q := 1 - (cell12698 ⟨45,by decide⟩).lower)
        (by norm_num [cell12698]) (by norm_num [cell12698])
      exact ⟨E.1,E.2.trans (by norm_num [cell12698])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy46 (n := 12698) (by norm_num)
        (q := 1 - (cell12698 ⟨46,by decide⟩).lower)
        (by norm_num [cell12698]) (by norm_num [cell12698])
      exact ⟨E.1,E.2.trans (by norm_num [cell12698])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy47 (n := 12698) (by norm_num)
        (q := 1 - (cell12698 ⟨47,by decide⟩).lower)
        (by norm_num [cell12698]) (by norm_num [cell12698])
      exact ⟨E.1,E.2.trans (by norm_num [cell12698])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy48 (n := 12698) (by norm_num)
        (q := 1 - (cell12698 ⟨48,by decide⟩).lower)
        (by norm_num [cell12698]) (by norm_num [cell12698])
      exact ⟨E.1,E.2.trans (by norm_num [cell12698])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy49 (n := 12698) (by norm_num)
        (q := 1 - (cell12698 ⟨49,by decide⟩).lower)
        (by norm_num [cell12698]) (by norm_num [cell12698])
      exact ⟨E.1,E.2.trans (by norm_num [cell12698])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy50 (n := 12698) (by norm_num)
        (q := 1 - (cell12698 ⟨50,by decide⟩).lower)
        (by norm_num [cell12698]) (by norm_num [cell12698])
      exact ⟨E.1,E.2.trans (by norm_num [cell12698])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy51 (n := 12698) (by norm_num)
        (q := 1 - (cell12698 ⟨51,by decide⟩).lower)
        (by norm_num [cell12698]) (by norm_num [cell12698])
      exact ⟨E.1,E.2.trans (by norm_num [cell12698])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy52 (n := 12698) (by norm_num)
        (q := 1 - (cell12698 ⟨52,by decide⟩).lower)
        (by norm_num [cell12698]) (by norm_num [cell12698])
      exact ⟨E.1,E.2.trans (by norm_num [cell12698])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12698

/-! Source-cell containment and simple scalar guards at 12698. -/
namespace BstLean.Part269.N12698
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12698)
open BstLean.Part268 (cell12698)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12698 ⟨10,by decide⟩).lower ∧ (cell12698 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12698 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12698 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12698 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12698 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12698 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12698,cell12698,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12698 ⟨11,by decide⟩).lower ∧ (cell12698 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12698 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12698 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12698 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12698 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12698 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12698,cell12698,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12698 ⟨12,by decide⟩).lower ∧ (cell12698 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12698 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12698 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12698 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12698 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12698 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12698,cell12698,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12698 ⟨13,by decide⟩).lower ∧ (cell12698 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12698 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12698 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12698 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12698 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12698 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12698,cell12698,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12698 ⟨14,by decide⟩).lower ∧ (cell12698 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12698 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12698 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12698 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12698 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12698 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12698,cell12698,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12698 ⟨15,by decide⟩).lower ∧ (cell12698 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12698 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12698 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12698 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12698 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12698 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12698,cell12698,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12698 ⟨16,by decide⟩).lower ∧ (cell12698 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12698 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12698 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12698 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12698 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12698 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12698,cell12698,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12698 ⟨17,by decide⟩).lower ∧ (cell12698 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12698 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12698 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12698 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12698 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12698 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12698,cell12698,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12698 ⟨18,by decide⟩).lower ∧ (cell12698 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12698 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12698 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12698 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12698 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12698 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12698,cell12698,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12698 ⟨19,by decide⟩).lower ∧ (cell12698 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12698 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12698 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12698 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12698 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12698 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12698,cell12698,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12698 ⟨20,by decide⟩).lower ∧ (cell12698 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12698 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12698 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12698 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12698 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12698 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12698,cell12698,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12698 ⟨21,by decide⟩).lower ∧ (cell12698 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12698 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12698 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12698 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12698 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12698 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12698,cell12698,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12698 ⟨22,by decide⟩).lower ∧ (cell12698 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12698 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12698 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12698 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12698 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12698 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12698,cell12698,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12698 ⟨23,by decide⟩).lower ∧ (cell12698 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12698 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12698 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12698 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12698 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12698 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12698,cell12698,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12698 ⟨24,by decide⟩).lower ∧ (cell12698 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12698 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12698 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12698 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12698 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12698 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12698,cell12698,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12698 ⟨25,by decide⟩).lower ∧ (cell12698 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12698 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12698 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12698 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12698 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12698 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12698,cell12698,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12698 ⟨26,by decide⟩).lower ∧ (cell12698 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12698 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12698 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12698 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12698 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12698 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12698,cell12698,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12698 ⟨27,by decide⟩).lower ∧ (cell12698 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12698 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12698 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12698 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12698 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12698 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12698,cell12698,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12698 ⟨28,by decide⟩).lower ∧ (cell12698 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12698 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12698 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12698 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12698 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12698 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12698,cell12698,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12698 ⟨29,by decide⟩).lower ∧ (cell12698 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12698 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12698 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12698 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12698 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12698 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12698,cell12698,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12698 ⟨30,by decide⟩).lower ∧ (cell12698 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12698 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12698 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12698 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12698 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12698 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12698,cell12698,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12698 ⟨31,by decide⟩).lower ∧ (cell12698 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12698 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12698 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12698 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12698 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12698 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12698,cell12698,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12698 ⟨32,by decide⟩).lower ∧ (cell12698 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12698 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12698 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12698 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12698 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12698 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12698,cell12698,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12698 ⟨33,by decide⟩).lower ∧ (cell12698 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12698 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12698 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12698 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12698 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12698 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12698,cell12698,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12698 ⟨34,by decide⟩).lower ∧ (cell12698 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12698 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12698 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12698 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12698 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12698 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12698,cell12698,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12698 ⟨35,by decide⟩).lower ∧ (cell12698 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12698 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12698 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12698 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12698 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12698 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12698,cell12698,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12698 ⟨36,by decide⟩).lower ∧ (cell12698 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12698 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12698 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12698 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12698 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12698 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12698,cell12698,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12698 ⟨37,by decide⟩).lower ∧ (cell12698 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12698 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12698 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12698 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12698 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12698 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12698,cell12698,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12698 ⟨38,by decide⟩).lower ∧ (cell12698 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12698 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12698 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12698 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12698 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12698 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12698,cell12698,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12698 ⟨39,by decide⟩).lower ∧ (cell12698 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12698 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12698 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12698 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12698 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12698 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12698,cell12698,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12698 ⟨40,by decide⟩).lower ∧ (cell12698 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12698 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12698 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12698 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12698 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12698 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12698,cell12698,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12698 ⟨41,by decide⟩).lower ∧ (cell12698 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12698 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12698 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12698 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12698 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12698 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12698,cell12698,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12698 ⟨42,by decide⟩).lower ∧ (cell12698 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12698 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12698 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12698 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12698 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12698 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12698,cell12698,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12698 ⟨43,by decide⟩).lower ∧ (cell12698 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12698 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12698 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12698 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12698 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12698 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12698,cell12698,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12698 ⟨44,by decide⟩).lower ∧ (cell12698 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12698 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12698 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12698 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12698 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12698 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12698,cell12698,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12698 ⟨45,by decide⟩).lower ∧ (cell12698 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12698 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12698 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12698 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12698 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12698 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12698,cell12698,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12698 ⟨46,by decide⟩).lower ∧ (cell12698 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12698 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12698 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12698 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12698 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12698 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12698,cell12698,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12698 ⟨47,by decide⟩).lower ∧ (cell12698 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12698 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12698 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12698 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12698 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12698 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12698,cell12698,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12698 ⟨48,by decide⟩).lower ∧ (cell12698 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12698 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12698 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12698 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12698 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12698 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12698,cell12698,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12698 ⟨49,by decide⟩).lower ∧ (cell12698 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12698 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12698 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12698 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12698 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12698 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12698,cell12698,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12698 ⟨50,by decide⟩).lower ∧ (cell12698 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12698 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12698 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12698 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12698 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12698 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12698,cell12698,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12698 ⟨51,by decide⟩).lower ∧ (cell12698 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12698 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12698 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12698 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12698 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12698 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12698,cell12698,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12698 ⟨52,by decide⟩).lower ∧ (cell12698 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12698 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12698 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12698 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12698 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12698 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12698,cell12698,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12698 i).lower ∧
    (cell12698 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12698 i).upper ≤ (0.532 : ℝ) ∧
    (cell12698 i).centre ≤ (0.1 : ℝ) ∧ (cell12698 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12698 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12698 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12698

/-! The local source numeric instances at 12698 have no network premises. -/
namespace BstLean.Part269.N12698
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12698)
open BstLean.Part268 (cell12698)

noncomputable def sourceNumerics12698 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12698 (cell12698 i)
      scalarRow12698.M scalarRow12698.H scalarRow12698.xi := by
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
    energy_allowance := scalarRow12698.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12698]
    centre_nonneg := (scalarRow12698.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D13.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12698])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12698
/-! Actual 12699 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12699
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12699 ≤ (1.035810643303 : ℝ) := by
  have hr : (112.689839825957 : ℝ) ≤ √(12699 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.689839825957 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12699 12699 (11 / 1000) ≤
    (0.008482459740 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12699) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.689839825957 : ℝ) ≤ √(12699 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12699)
  have hdiv : K / √(12699 : ℝ) ≤ K / 112.689839825957 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.689839825957 ≤ (0.008482459740 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12699.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12699 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12699 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12699 := gPlus_lower 12699
end BstLean.Part269.N12699

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12699
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035810643302 : ℝ) ≤ wn 12699 := by
  have hn : √(12699 : ℝ) ≤ 112.689839825958 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12699 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.689839825958 ≤ 2 / √(12699 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000251901050 : ℝ) ≤ rhoBar 12699 BstLean.Part154.csC ∧
    rhoBar 12699 BstLean.Part154.csC ≤ 0.000251901440 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035810643302 : ℝ) / (1.295212 * 12699) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035810643303 : ℝ) / (1.29521 * 12699) := by gcongr
      _ ≤ (0.000251901440 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12699 BstLean.Part154.csC) ≤ 0.001007669215 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12699 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12699 BstLean.Part154.csC) (piBar (rhoBar 12699 BstLean.Part154.csC)) ≤ 0.000192404020 ∧
    cc1 (rhoBar 12699 BstLean.Part154.csC) (piBar (rhoBar 12699 BstLean.Part154.csC)) ≤ 0.000122427955 ∧
    cc2 (rhoBar 12699 BstLean.Part154.csC) ≤ 0.000071070366 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12699 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12699 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12699 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12699 BstLean.Part154.csC * nuR (rhoBar 12699 BstLean.Part154.csC)) ≤ 0.000503818744 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000251901440 : ℝ) * 0.001007669215 := by gcongr
      _ ≤ (0.000503818744 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12699 BstLean.Part154.csC) * nuR (rhoBar 12699 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001007669215 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12699 BstLean.Part154.csC) * rhoBar 12699 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000251901440 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000251901440 / 2 + 0.399 * 0.001007669215 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000192404020 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000503818744 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122427955 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000251901440 / 1.414213562 := by gcongr
      _ ≤ (0.000071070366 : ℝ) := by norm_num

end BstLean.Part269.N12699

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12699
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12699 BstLean.Part154.csC) (piBar (rhoBar 12699 BstLean.Part154.csC)) ≤ 1.59869E-7 := by
  have hr0 : 0 ≤ rhoBar 12699 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12699 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12699 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12699 BstLean.Part154.csC) (piBar (rhoBar 12699 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12699 BstLean.Part154.csC) (piBar (rhoBar 12699 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12699 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000192404020 : ℝ) ^ 2 + 0.000122427955 ^ 2 + 3 * 0.000071070366 ^ 2 +
        2 * 0.797885 * 0.000192404020 * 0.000122427955 + 2 * 0.000192404020 * 0.000071070366 +
        4 * 0.797885 * 0.000122427955 * 0.000071070366 := by gcongr
    _ ≤ (1.59869E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12699 BstLean.Part154.csC Θ ≤ 0.002629508877 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12699 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12699 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12699 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12699 BstLean.Part154.csC) (piBar (rhoBar 12699 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12699 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035810643303 * 1.59869E-7 / (0.000251901050 : ℝ) := by gcongr
    _ ≤ 0.002629508877 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12699 BstLean.Part154.csC Θ ≤ 0.002917579785 + 0.000664433046 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12699 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12699 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12699 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035810643303 : ℝ) * ((2 * Θ * 0.000251901440 +
        (6863 / 10000) * 0.000251901440 * 12699 * 0.001007669215) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002917579785 + 0.000664433046 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12699 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12699 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12699 0.011 Θ ∧ gammaRatio 12699 0.011 Θ ≤ 0.000086597201 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12699 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035810643303 : ℝ) * 0.525 / ((1 - 0.011) * 12699) := by gcongr
      _ ≤ (0.000086597201 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12699 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12699 0.011 Θ) :=
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
    badAllowance 12699 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000615501984 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12699 BstLean.Part154.csC) 1.22 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 2 (rhoBar 12699 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12699 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12699 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12699 0.011 Θ) 1.12 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 1 (gammaRatio 12699 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12699 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12699 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12699 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12699 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035810643303 : ℝ) * 12699 *
        (2.2721E-8 / 1.1045361 + 2.7751E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000615501984 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12699 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003533081769 + 0.003293941923 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12699

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12699
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12699 BstLean.Part154.csC) (piBar (rhoBar 12699 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12699 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12699 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12699 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12699 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12699 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12699 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12699 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12699 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12699 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12699 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12699 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12699 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12699 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12699 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052486401639 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12699) ≤ 0.010597562149 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12699 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035810643303)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010597562149 + 2 * 0.737676 / 12699) := by gcongr
    _ ≤ (0.052486401639 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12699 12 ≤ 0.0015 := by
  exact BstLean.Part269.S13.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12699

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12699
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560503523064 : ℝ) ≤ plow 12699 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12699) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052769001279)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001380492161) : eMP 12699 0.011 xi bn ≤ 0.001188473378 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12699 : ℝ) * (1 - 0.011))) ≤ 0.000587636855 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001380492161 / (12699 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000587636855 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000587636855 : ℝ) + 3.141593 * 0.052769001279 / (12699 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001188473378 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052769001279)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001380492161) : PiBarMP 12699 12 0.011 xi bn ≤ 0.161257510969 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12699 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037154974916 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.068331833752 : ℝ) ≤ √((12699 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.689839825957 : ℝ) ≤ √(12699 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12699) ≤ 0.123634999254 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037154974916 + 0.052769001279 * 1.772454 / (2 * (112.068331833752 : ℝ))) * (1 + 0.001188473378) +
        8 / (12699 * 112.689839825957) + 0.123634999254 := by gcongr
    _ ≤ (0.161257510969 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052769001279)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001380492161) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282201445289) :
    parallelOracle 12699 0.011 xi bn cd ≤ 0.162248159410 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12699 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12699 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560503523064 : ℝ) ≤ plow 12699 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.689839825957 : ℝ) ≤ √(12699 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282201445289 : ℝ) / (2 * 0.560503523064 * 112.689839825957)) * 0.161257510969 +
        0.282201445289 ^ 2 / (2 * 0.560503523064 * 112.689839825957) := by gcongr
    _ ≤ (0.162248159410 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052769001279) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001380492161)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282201445289) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12699 12699 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560503523064 : ℝ) ≤ plow 12699 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.689839825957 : ℝ) ≤ √(12699 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12699 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12699 Θ 1.22 ≤ 0.011767702413 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.689839825957 := by gcongr <;> linarith
      _ ≤ (0.011767702413 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12699 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12699 12699 0.011 ≤ 0.008482459740 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12699 12699 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12699 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12699 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12699 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12699 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162248159410 + 0.011767702413 + (0.008482459740 : ℝ) *
        (1 + 2 * (0.282201445289 + 0.011767702413) / (0.560503523064 * 112.689839825957))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12699]

end BstLean.Part269.N12699

/-! The original eight local profiles supply actual 12699 moment certificates. -/
namespace BstLean.Part269.N12699
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12699 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12699 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12699 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052769001279 ∧
    0 ≤ bN 12699 BstLean.Part154.csC (groupTheta g) ∧ bN 12699 BstLean.Part154.csC (groupTheta g) ≤ 0.001380492161 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12699 12699 0.011
      (momentAllowance 12699 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12699 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12699 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12699 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12699 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12699 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229715043650 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12699 0.011
      (momentAllowance 12699 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12699 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12699
/-! The actual computed-centre upper energy formula at 12699. -/
namespace BstLean.Part269.N12699
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12699

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12699
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12699)
open BstLean.Part268 (cell12699)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085493173048
  | 2 => 0.086435975913
  | 3 => 0.087376926229
  | 4 => 0.088317443858
  | 5 => 0.089259246142
  | 6 => 0.090204392081
  | 7 => 0.091155330664
  | 8 => 0.092114953401
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12699 12699 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12699 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003538895953 + 0.003300387184 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S13.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12699

/-! Actual upper energy certificates on all 43 source endpoints at 12699. -/
namespace BstLean.Part269.N12699
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12699)
open BstLean.Part268 (cell12699)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12699 (gMinus 12699) (1 - (cell12699 i).lower) ≤ 1 ∧
    energyUpper 12699 (gMinus 12699) (BstLean.Part211.gPlus 12699)
      (finiteEnergy 12699 12699 0.011) (1 - (cell12699 i).lower) ≤
      (cell12699 i).energy := by
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
      have E := BstLean.Part269.S13.uniformEnergy10 (n := 12699) (by norm_num)
        (q := 1 - (cell12699 ⟨10,by decide⟩).lower)
        (by norm_num [cell12699]) (by norm_num [cell12699])
      exact ⟨E.1,E.2.trans (by norm_num [cell12699])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy11 (n := 12699) (by norm_num)
        (q := 1 - (cell12699 ⟨11,by decide⟩).lower)
        (by norm_num [cell12699]) (by norm_num [cell12699])
      exact ⟨E.1,E.2.trans (by norm_num [cell12699])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy12 (n := 12699) (by norm_num)
        (q := 1 - (cell12699 ⟨12,by decide⟩).lower)
        (by norm_num [cell12699]) (by norm_num [cell12699])
      exact ⟨E.1,E.2.trans (by norm_num [cell12699])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy13 (n := 12699) (by norm_num)
        (q := 1 - (cell12699 ⟨13,by decide⟩).lower)
        (by norm_num [cell12699]) (by norm_num [cell12699])
      exact ⟨E.1,E.2.trans (by norm_num [cell12699])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy14 (n := 12699) (by norm_num)
        (q := 1 - (cell12699 ⟨14,by decide⟩).lower)
        (by norm_num [cell12699]) (by norm_num [cell12699])
      exact ⟨E.1,E.2.trans (by norm_num [cell12699])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy15 (n := 12699) (by norm_num)
        (q := 1 - (cell12699 ⟨15,by decide⟩).lower)
        (by norm_num [cell12699]) (by norm_num [cell12699])
      exact ⟨E.1,E.2.trans (by norm_num [cell12699])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy16 (n := 12699) (by norm_num)
        (q := 1 - (cell12699 ⟨16,by decide⟩).lower)
        (by norm_num [cell12699]) (by norm_num [cell12699])
      exact ⟨E.1,E.2.trans (by norm_num [cell12699])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy17 (n := 12699) (by norm_num)
        (q := 1 - (cell12699 ⟨17,by decide⟩).lower)
        (by norm_num [cell12699]) (by norm_num [cell12699])
      exact ⟨E.1,E.2.trans (by norm_num [cell12699])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy18 (n := 12699) (by norm_num)
        (q := 1 - (cell12699 ⟨18,by decide⟩).lower)
        (by norm_num [cell12699]) (by norm_num [cell12699])
      exact ⟨E.1,E.2.trans (by norm_num [cell12699])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy19 (n := 12699) (by norm_num)
        (q := 1 - (cell12699 ⟨19,by decide⟩).lower)
        (by norm_num [cell12699]) (by norm_num [cell12699])
      exact ⟨E.1,E.2.trans (by norm_num [cell12699])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy20 (n := 12699) (by norm_num)
        (q := 1 - (cell12699 ⟨20,by decide⟩).lower)
        (by norm_num [cell12699]) (by norm_num [cell12699])
      exact ⟨E.1,E.2.trans (by norm_num [cell12699])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy21 (n := 12699) (by norm_num)
        (q := 1 - (cell12699 ⟨21,by decide⟩).lower)
        (by norm_num [cell12699]) (by norm_num [cell12699])
      exact ⟨E.1,E.2.trans (by norm_num [cell12699])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy22 (n := 12699) (by norm_num)
        (q := 1 - (cell12699 ⟨22,by decide⟩).lower)
        (by norm_num [cell12699]) (by norm_num [cell12699])
      exact ⟨E.1,E.2.trans (by norm_num [cell12699])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy23 (n := 12699) (by norm_num)
        (q := 1 - (cell12699 ⟨23,by decide⟩).lower)
        (by norm_num [cell12699]) (by norm_num [cell12699])
      exact ⟨E.1,E.2.trans (by norm_num [cell12699])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy24 (n := 12699) (by norm_num)
        (q := 1 - (cell12699 ⟨24,by decide⟩).lower)
        (by norm_num [cell12699]) (by norm_num [cell12699])
      exact ⟨E.1,E.2.trans (by norm_num [cell12699])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy25 (n := 12699) (by norm_num)
        (q := 1 - (cell12699 ⟨25,by decide⟩).lower)
        (by norm_num [cell12699]) (by norm_num [cell12699])
      exact ⟨E.1,E.2.trans (by norm_num [cell12699])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy26 (n := 12699) (by norm_num)
        (q := 1 - (cell12699 ⟨26,by decide⟩).lower)
        (by norm_num [cell12699]) (by norm_num [cell12699])
      exact ⟨E.1,E.2.trans (by norm_num [cell12699])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy27 (n := 12699) (by norm_num)
        (q := 1 - (cell12699 ⟨27,by decide⟩).lower)
        (by norm_num [cell12699]) (by norm_num [cell12699])
      exact ⟨E.1,E.2.trans (by norm_num [cell12699])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy28 (n := 12699) (by norm_num)
        (q := 1 - (cell12699 ⟨28,by decide⟩).lower)
        (by norm_num [cell12699]) (by norm_num [cell12699])
      exact ⟨E.1,E.2.trans (by norm_num [cell12699])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy29 (n := 12699) (by norm_num)
        (q := 1 - (cell12699 ⟨29,by decide⟩).lower)
        (by norm_num [cell12699]) (by norm_num [cell12699])
      exact ⟨E.1,E.2.trans (by norm_num [cell12699])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy30 (n := 12699) (by norm_num)
        (q := 1 - (cell12699 ⟨30,by decide⟩).lower)
        (by norm_num [cell12699]) (by norm_num [cell12699])
      exact ⟨E.1,E.2.trans (by norm_num [cell12699])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy31 (n := 12699) (by norm_num)
        (q := 1 - (cell12699 ⟨31,by decide⟩).lower)
        (by norm_num [cell12699]) (by norm_num [cell12699])
      exact ⟨E.1,E.2.trans (by norm_num [cell12699])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy32 (n := 12699) (by norm_num)
        (q := 1 - (cell12699 ⟨32,by decide⟩).lower)
        (by norm_num [cell12699]) (by norm_num [cell12699])
      exact ⟨E.1,E.2.trans (by norm_num [cell12699])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy33 (n := 12699) (by norm_num)
        (q := 1 - (cell12699 ⟨33,by decide⟩).lower)
        (by norm_num [cell12699]) (by norm_num [cell12699])
      exact ⟨E.1,E.2.trans (by norm_num [cell12699])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy34 (n := 12699) (by norm_num)
        (q := 1 - (cell12699 ⟨34,by decide⟩).lower)
        (by norm_num [cell12699]) (by norm_num [cell12699])
      exact ⟨E.1,E.2.trans (by norm_num [cell12699])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy35 (n := 12699) (by norm_num)
        (q := 1 - (cell12699 ⟨35,by decide⟩).lower)
        (by norm_num [cell12699]) (by norm_num [cell12699])
      exact ⟨E.1,E.2.trans (by norm_num [cell12699])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy36 (n := 12699) (by norm_num)
        (q := 1 - (cell12699 ⟨36,by decide⟩).lower)
        (by norm_num [cell12699]) (by norm_num [cell12699])
      exact ⟨E.1,E.2.trans (by norm_num [cell12699])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy37 (n := 12699) (by norm_num)
        (q := 1 - (cell12699 ⟨37,by decide⟩).lower)
        (by norm_num [cell12699]) (by norm_num [cell12699])
      exact ⟨E.1,E.2.trans (by norm_num [cell12699])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy38 (n := 12699) (by norm_num)
        (q := 1 - (cell12699 ⟨38,by decide⟩).lower)
        (by norm_num [cell12699]) (by norm_num [cell12699])
      exact ⟨E.1,E.2.trans (by norm_num [cell12699])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy39 (n := 12699) (by norm_num)
        (q := 1 - (cell12699 ⟨39,by decide⟩).lower)
        (by norm_num [cell12699]) (by norm_num [cell12699])
      exact ⟨E.1,E.2.trans (by norm_num [cell12699])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy40 (n := 12699) (by norm_num)
        (q := 1 - (cell12699 ⟨40,by decide⟩).lower)
        (by norm_num [cell12699]) (by norm_num [cell12699])
      exact ⟨E.1,E.2.trans (by norm_num [cell12699])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy41 (n := 12699) (by norm_num)
        (q := 1 - (cell12699 ⟨41,by decide⟩).lower)
        (by norm_num [cell12699]) (by norm_num [cell12699])
      exact ⟨E.1,E.2.trans (by norm_num [cell12699])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy42 (n := 12699) (by norm_num)
        (q := 1 - (cell12699 ⟨42,by decide⟩).lower)
        (by norm_num [cell12699]) (by norm_num [cell12699])
      exact ⟨E.1,E.2.trans (by norm_num [cell12699])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy43 (n := 12699) (by norm_num)
        (q := 1 - (cell12699 ⟨43,by decide⟩).lower)
        (by norm_num [cell12699]) (by norm_num [cell12699])
      exact ⟨E.1,E.2.trans (by norm_num [cell12699])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy44 (n := 12699) (by norm_num)
        (q := 1 - (cell12699 ⟨44,by decide⟩).lower)
        (by norm_num [cell12699]) (by norm_num [cell12699])
      exact ⟨E.1,E.2.trans (by norm_num [cell12699])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy45 (n := 12699) (by norm_num)
        (q := 1 - (cell12699 ⟨45,by decide⟩).lower)
        (by norm_num [cell12699]) (by norm_num [cell12699])
      exact ⟨E.1,E.2.trans (by norm_num [cell12699])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy46 (n := 12699) (by norm_num)
        (q := 1 - (cell12699 ⟨46,by decide⟩).lower)
        (by norm_num [cell12699]) (by norm_num [cell12699])
      exact ⟨E.1,E.2.trans (by norm_num [cell12699])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy47 (n := 12699) (by norm_num)
        (q := 1 - (cell12699 ⟨47,by decide⟩).lower)
        (by norm_num [cell12699]) (by norm_num [cell12699])
      exact ⟨E.1,E.2.trans (by norm_num [cell12699])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy48 (n := 12699) (by norm_num)
        (q := 1 - (cell12699 ⟨48,by decide⟩).lower)
        (by norm_num [cell12699]) (by norm_num [cell12699])
      exact ⟨E.1,E.2.trans (by norm_num [cell12699])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy49 (n := 12699) (by norm_num)
        (q := 1 - (cell12699 ⟨49,by decide⟩).lower)
        (by norm_num [cell12699]) (by norm_num [cell12699])
      exact ⟨E.1,E.2.trans (by norm_num [cell12699])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy50 (n := 12699) (by norm_num)
        (q := 1 - (cell12699 ⟨50,by decide⟩).lower)
        (by norm_num [cell12699]) (by norm_num [cell12699])
      exact ⟨E.1,E.2.trans (by norm_num [cell12699])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy51 (n := 12699) (by norm_num)
        (q := 1 - (cell12699 ⟨51,by decide⟩).lower)
        (by norm_num [cell12699]) (by norm_num [cell12699])
      exact ⟨E.1,E.2.trans (by norm_num [cell12699])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy52 (n := 12699) (by norm_num)
        (q := 1 - (cell12699 ⟨52,by decide⟩).lower)
        (by norm_num [cell12699]) (by norm_num [cell12699])
      exact ⟨E.1,E.2.trans (by norm_num [cell12699])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12699

/-! Source-cell containment and simple scalar guards at 12699. -/
namespace BstLean.Part269.N12699
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12699)
open BstLean.Part268 (cell12699)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12699 ⟨10,by decide⟩).lower ∧ (cell12699 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12699 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12699 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12699 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12699 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12699 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12699,cell12699,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12699 ⟨11,by decide⟩).lower ∧ (cell12699 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12699 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12699 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12699 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12699 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12699 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12699,cell12699,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12699 ⟨12,by decide⟩).lower ∧ (cell12699 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12699 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12699 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12699 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12699 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12699 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12699,cell12699,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12699 ⟨13,by decide⟩).lower ∧ (cell12699 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12699 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12699 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12699 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12699 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12699 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12699,cell12699,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12699 ⟨14,by decide⟩).lower ∧ (cell12699 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12699 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12699 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12699 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12699 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12699 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12699,cell12699,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12699 ⟨15,by decide⟩).lower ∧ (cell12699 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12699 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12699 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12699 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12699 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12699 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12699,cell12699,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12699 ⟨16,by decide⟩).lower ∧ (cell12699 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12699 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12699 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12699 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12699 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12699 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12699,cell12699,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12699 ⟨17,by decide⟩).lower ∧ (cell12699 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12699 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12699 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12699 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12699 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12699 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12699,cell12699,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12699 ⟨18,by decide⟩).lower ∧ (cell12699 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12699 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12699 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12699 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12699 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12699 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12699,cell12699,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12699 ⟨19,by decide⟩).lower ∧ (cell12699 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12699 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12699 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12699 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12699 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12699 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12699,cell12699,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12699 ⟨20,by decide⟩).lower ∧ (cell12699 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12699 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12699 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12699 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12699 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12699 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12699,cell12699,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12699 ⟨21,by decide⟩).lower ∧ (cell12699 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12699 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12699 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12699 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12699 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12699 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12699,cell12699,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12699 ⟨22,by decide⟩).lower ∧ (cell12699 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12699 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12699 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12699 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12699 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12699 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12699,cell12699,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12699 ⟨23,by decide⟩).lower ∧ (cell12699 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12699 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12699 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12699 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12699 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12699 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12699,cell12699,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12699 ⟨24,by decide⟩).lower ∧ (cell12699 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12699 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12699 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12699 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12699 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12699 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12699,cell12699,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12699 ⟨25,by decide⟩).lower ∧ (cell12699 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12699 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12699 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12699 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12699 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12699 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12699,cell12699,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12699 ⟨26,by decide⟩).lower ∧ (cell12699 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12699 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12699 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12699 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12699 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12699 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12699,cell12699,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12699 ⟨27,by decide⟩).lower ∧ (cell12699 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12699 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12699 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12699 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12699 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12699 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12699,cell12699,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12699 ⟨28,by decide⟩).lower ∧ (cell12699 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12699 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12699 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12699 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12699 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12699 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12699,cell12699,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12699 ⟨29,by decide⟩).lower ∧ (cell12699 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12699 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12699 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12699 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12699 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12699 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12699,cell12699,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12699 ⟨30,by decide⟩).lower ∧ (cell12699 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12699 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12699 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12699 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12699 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12699 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12699,cell12699,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12699 ⟨31,by decide⟩).lower ∧ (cell12699 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12699 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12699 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12699 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12699 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12699 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12699,cell12699,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12699 ⟨32,by decide⟩).lower ∧ (cell12699 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12699 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12699 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12699 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12699 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12699 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12699,cell12699,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12699 ⟨33,by decide⟩).lower ∧ (cell12699 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12699 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12699 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12699 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12699 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12699 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12699,cell12699,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12699 ⟨34,by decide⟩).lower ∧ (cell12699 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12699 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12699 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12699 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12699 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12699 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12699,cell12699,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12699 ⟨35,by decide⟩).lower ∧ (cell12699 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12699 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12699 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12699 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12699 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12699 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12699,cell12699,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12699 ⟨36,by decide⟩).lower ∧ (cell12699 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12699 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12699 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12699 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12699 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12699 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12699,cell12699,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12699 ⟨37,by decide⟩).lower ∧ (cell12699 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12699 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12699 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12699 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12699 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12699 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12699,cell12699,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12699 ⟨38,by decide⟩).lower ∧ (cell12699 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12699 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12699 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12699 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12699 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12699 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12699,cell12699,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12699 ⟨39,by decide⟩).lower ∧ (cell12699 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12699 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12699 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12699 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12699 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12699 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12699,cell12699,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12699 ⟨40,by decide⟩).lower ∧ (cell12699 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12699 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12699 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12699 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12699 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12699 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12699,cell12699,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12699 ⟨41,by decide⟩).lower ∧ (cell12699 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12699 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12699 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12699 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12699 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12699 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12699,cell12699,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12699 ⟨42,by decide⟩).lower ∧ (cell12699 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12699 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12699 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12699 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12699 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12699 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12699,cell12699,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12699 ⟨43,by decide⟩).lower ∧ (cell12699 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12699 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12699 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12699 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12699 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12699 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12699,cell12699,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12699 ⟨44,by decide⟩).lower ∧ (cell12699 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12699 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12699 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12699 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12699 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12699 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12699,cell12699,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12699 ⟨45,by decide⟩).lower ∧ (cell12699 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12699 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12699 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12699 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12699 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12699 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12699,cell12699,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12699 ⟨46,by decide⟩).lower ∧ (cell12699 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12699 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12699 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12699 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12699 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12699 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12699,cell12699,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12699 ⟨47,by decide⟩).lower ∧ (cell12699 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12699 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12699 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12699 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12699 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12699 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12699,cell12699,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12699 ⟨48,by decide⟩).lower ∧ (cell12699 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12699 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12699 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12699 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12699 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12699 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12699,cell12699,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12699 ⟨49,by decide⟩).lower ∧ (cell12699 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12699 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12699 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12699 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12699 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12699 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12699,cell12699,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12699 ⟨50,by decide⟩).lower ∧ (cell12699 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12699 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12699 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12699 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12699 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12699 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12699,cell12699,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12699 ⟨51,by decide⟩).lower ∧ (cell12699 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12699 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12699 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12699 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12699 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12699 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12699,cell12699,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12699 ⟨52,by decide⟩).lower ∧ (cell12699 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12699 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12699 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12699 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12699 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12699 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12699,cell12699,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12699 i).lower ∧
    (cell12699 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12699 i).upper ≤ (0.532 : ℝ) ∧
    (cell12699 i).centre ≤ (0.1 : ℝ) ∧ (cell12699 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12699 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12699 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12699

/-! The local source numeric instances at 12699 have no network premises. -/
namespace BstLean.Part269.N12699
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12699)
open BstLean.Part268 (cell12699)

noncomputable def sourceNumerics12699 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12699 (cell12699 i)
      scalarRow12699.M scalarRow12699.H scalarRow12699.xi := by
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
    energy_allowance := scalarRow12699.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12699]
    centre_nonneg := (scalarRow12699.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D13.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12699])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12699