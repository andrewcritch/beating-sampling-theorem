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
/-! Actual 12600 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12600
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12600 ≤ (1.035952292573 : ℝ) := by
  have hr : (112.249721603218 : ℝ) ≤ √(12600 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.249721603218 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12600 12600 (11 / 1000) ≤
    (0.008515718744 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12600) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.249721603218 : ℝ) ≤ √(12600 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12600)
  have hdiv : K / √(12600 : ℝ) ≤ K / 112.249721603218 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.249721603218 ≤ (0.008515718744 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12600.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12600 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12600 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12600 := gPlus_lower 12600
end BstLean.Part269.N12600

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12600
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035952292572 : ℝ) ≤ wn 12600 := by
  have hn : √(12600 : ℝ) ≤ 112.249721603219 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12600 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.249721603219 ≤ 2 / √(12600 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000253914991 : ℝ) ≤ rhoBar 12600 BstLean.Part154.csC ∧
    rhoBar 12600 BstLean.Part154.csC ≤ 0.000253915384 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035952292572 : ℝ) / (1.295212 * 12600) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035952292573 : ℝ) / (1.29521 * 12600) := by gcongr
      _ ≤ (0.000253915384 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12600 BstLean.Part154.csC) ≤ 0.001015726010 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12600 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12600 BstLean.Part154.csC) (piBar (rhoBar 12600 BstLean.Part154.csC)) ≤ 0.000193942356 ∧
    cc1 (rhoBar 12600 BstLean.Part154.csC) (piBar (rhoBar 12600 BstLean.Part154.csC)) ≤ 0.000123406794 ∧
    cc2 (rhoBar 12600 BstLean.Part154.csC) ≤ 0.000071638571 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12600 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12600 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12600 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12600 BstLean.Part154.csC * nuR (rhoBar 12600 BstLean.Part154.csC)) ≤ 0.000507846887 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000253915384 : ℝ) * 0.001015726010 := by gcongr
      _ ≤ (0.000507846887 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12600 BstLean.Part154.csC) * nuR (rhoBar 12600 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001015726010 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12600 BstLean.Part154.csC) * rhoBar 12600 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000253915384 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000253915384 / 2 + 0.399 * 0.001015726010 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000193942356 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000507846887 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123406794 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000253915384 / 1.414213562 := by gcongr
      _ ≤ (0.000071638571 : ℝ) := by norm_num

end BstLean.Part269.N12600

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12600
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12600 BstLean.Part154.csC) (piBar (rhoBar 12600 BstLean.Part154.csC)) ≤ 1.62435E-7 := by
  have hr0 : 0 ≤ rhoBar 12600 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12600 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12600 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12600 BstLean.Part154.csC) (piBar (rhoBar 12600 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12600 BstLean.Part154.csC) (piBar (rhoBar 12600 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12600 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000193942356 : ℝ) ^ 2 + 0.000123406794 ^ 2 + 3 * 0.000071638571 ^ 2 +
        2 * 0.797885 * 0.000193942356 * 0.000123406794 + 2 * 0.000193942356 * 0.000071638571 +
        4 * 0.797885 * 0.000123406794 * 0.000071638571 := by gcongr
    _ ≤ (1.62435E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12600 BstLean.Part154.csC Θ ≤ 0.002650885795 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12600 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12600 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12600 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12600 BstLean.Part154.csC) (piBar (rhoBar 12600 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12600 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035952292573 * 1.62435E-7 / (0.000253914991 : ℝ) := by gcongr
    _ ≤ 0.002650885795 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12600 BstLean.Part154.csC Θ ≤ 0.002941711626 + 0.000669836756 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12600 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12600 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12600 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035952292573 : ℝ) * ((2 * Θ * 0.000253915384 +
        (6863 / 10000) * 0.000253915384 * 12600 * 0.001015726010) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002941711626 + 0.000669836756 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12600 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12600 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12600 0.011 Θ ∧ gammaRatio 12600 0.011 Θ ≤ 0.000087289543 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12600 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035952292573 : ℝ) * 0.525 / ((1 - 0.011) * 12600) := by gcongr
      _ ≤ (0.000087289543 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12600 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12600 0.011 Θ) :=
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
    badAllowance 12600 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000676285396 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12600 BstLean.Part154.csC) 1.22 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 2 (rhoBar 12600 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12600 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12600 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12600 0.011 Θ) 1.12 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 1 (gammaRatio 12600 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12600 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12600 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12600 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12600 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035952292573 : ℝ) * 12600 *
        (2.5110E-8 / 1.1045361 + 3.0670E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000676285396 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12600 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003617997022 + 0.003320722551 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12600

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12600
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12600 BstLean.Part154.csC) (piBar (rhoBar 12600 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12600 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12600 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12600 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12600 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12600 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12600 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12600 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12600 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12600 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12600 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12600 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12600 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12600 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12600 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052694435119 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12600) ≤ 0.010639113969 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12600 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035952292573)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010639113969 + 2 * 0.737676 / 12600) := by gcongr
    _ ≤ (0.052694435119 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12600 12 ≤ 0.0015 := by
  exact BstLean.Part269.S10.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12600

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12600
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560499010103 : ℝ) ≤ plow 12600 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12600) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052867976362)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001391715043) : eMP 12600 0.011 xi bn ≤ 0.001197996444 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12600 : ℝ) * (1 - 0.011))) ≤ 0.000592334056 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001391715043 / (12600 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000592334056 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000592334056 : ℝ) + 3.141593 * 0.052867976362 / (12600 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001197996444 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052867976362)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001391715043) : PiBarMP 12600 12 0.011 xi bn ≤ 0.161896021027 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12600 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037305697193 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.630640954891 : ℝ) ≤ √((12600 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.249721603218 : ℝ) ≤ √(12600 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12600) ≤ 0.124119757838 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037305697193 + 0.052867976362 * 1.772454 / (2 * (111.630640954891 : ℝ))) * (1 + 0.001197996444) +
        8 / (12600 * 112.249721603218) + 0.124119757838 := by gcongr
    _ ≤ (0.161896021027 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052867976362)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001391715043) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282624807976) :
    parallelOracle 12600 0.011 xi bn cd ≤ 0.162894438742 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12600 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12600 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560499010103 : ℝ) ≤ plow 12600 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.249721603218 : ℝ) ≤ √(12600 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282624807976 : ℝ) / (2 * 0.560499010103 * 112.249721603218)) * 0.161896021027 +
        0.282624807976 ^ 2 / (2 * 0.560499010103 * 112.249721603218) := by gcongr
    _ ≤ (0.162894438742 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052867976362) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001391715043)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282624807976) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12600 12600 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560499010103 : ℝ) ≤ plow 12600 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.249721603218 : ℝ) ≤ √(12600 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12600 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12600 Θ 1.22 ≤ 0.011813842218 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.249721603218 := by gcongr <;> linarith
      _ ≤ (0.011813842218 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12600 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12600 12600 0.011 ≤ 0.008515718744 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12600 12600 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12600 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12600 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12600 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12600 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162894438742 + 0.011813842218 + (0.008515718744 : ℝ) *
        (1 + 2 * (0.282624807976 + 0.011813842218) / (0.560499010103 * 112.249721603218))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12600]

end BstLean.Part269.N12600

/-! The original eight local profiles supply actual 12600 moment certificates. -/
namespace BstLean.Part269.N12600
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12600 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12600 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12600 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052867976362 ∧
    0 ≤ bN 12600 BstLean.Part154.csC (groupTheta g) ∧ bN 12600 BstLean.Part154.csC (groupTheta g) ≤ 0.001391715043 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12600 12600 0.011
      (momentAllowance 12600 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12600 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12600 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12600 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12600 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12600 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229930372857 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12600 0.011
      (momentAllowance 12600 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12600 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12600
/-! The actual computed-centre upper energy formula at 12600. -/
namespace BstLean.Part269.N12600
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12600

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12600
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12600)
open BstLean.Part268 (cell12600)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085787494436
  | 2 => 0.086735833959
  | 3 => 0.087683149317
  | 4 => 0.088631049679
  | 5 => 0.089581474846
  | 6 => 0.090536743505
  | 7 => 0.091499605848
  | 8 => 0.092473300604
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12600 12600 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12600 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12600

/-! Actual upper energy certificates on all 43 source endpoints at 12600. -/
namespace BstLean.Part269.N12600
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12600)
open BstLean.Part268 (cell12600)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12600 (gMinus 12600) (1 - (cell12600 i).lower) ≤ 1 ∧
    energyUpper 12600 (gMinus 12600) (BstLean.Part211.gPlus 12600)
      (finiteEnergy 12600 12600 0.011) (1 - (cell12600 i).lower) ≤
      (cell12600 i).energy := by
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
      have E := BstLean.Part269.S10.uniformEnergy10 (n := 12600) (by norm_num)
        (q := 1 - (cell12600 ⟨10,by decide⟩).lower)
        (by norm_num [cell12600]) (by norm_num [cell12600])
      exact ⟨E.1,E.2.trans (by norm_num [cell12600])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy11 (n := 12600) (by norm_num)
        (q := 1 - (cell12600 ⟨11,by decide⟩).lower)
        (by norm_num [cell12600]) (by norm_num [cell12600])
      exact ⟨E.1,E.2.trans (by norm_num [cell12600])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy12 (n := 12600) (by norm_num)
        (q := 1 - (cell12600 ⟨12,by decide⟩).lower)
        (by norm_num [cell12600]) (by norm_num [cell12600])
      exact ⟨E.1,E.2.trans (by norm_num [cell12600])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy13 (n := 12600) (by norm_num)
        (q := 1 - (cell12600 ⟨13,by decide⟩).lower)
        (by norm_num [cell12600]) (by norm_num [cell12600])
      exact ⟨E.1,E.2.trans (by norm_num [cell12600])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy14 (n := 12600) (by norm_num)
        (q := 1 - (cell12600 ⟨14,by decide⟩).lower)
        (by norm_num [cell12600]) (by norm_num [cell12600])
      exact ⟨E.1,E.2.trans (by norm_num [cell12600])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy15 (n := 12600) (by norm_num)
        (q := 1 - (cell12600 ⟨15,by decide⟩).lower)
        (by norm_num [cell12600]) (by norm_num [cell12600])
      exact ⟨E.1,E.2.trans (by norm_num [cell12600])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy16 (n := 12600) (by norm_num)
        (q := 1 - (cell12600 ⟨16,by decide⟩).lower)
        (by norm_num [cell12600]) (by norm_num [cell12600])
      exact ⟨E.1,E.2.trans (by norm_num [cell12600])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy17 (n := 12600) (by norm_num)
        (q := 1 - (cell12600 ⟨17,by decide⟩).lower)
        (by norm_num [cell12600]) (by norm_num [cell12600])
      exact ⟨E.1,E.2.trans (by norm_num [cell12600])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy18 (n := 12600) (by norm_num)
        (q := 1 - (cell12600 ⟨18,by decide⟩).lower)
        (by norm_num [cell12600]) (by norm_num [cell12600])
      exact ⟨E.1,E.2.trans (by norm_num [cell12600])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy19 (n := 12600) (by norm_num)
        (q := 1 - (cell12600 ⟨19,by decide⟩).lower)
        (by norm_num [cell12600]) (by norm_num [cell12600])
      exact ⟨E.1,E.2.trans (by norm_num [cell12600])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy20 (n := 12600) (by norm_num)
        (q := 1 - (cell12600 ⟨20,by decide⟩).lower)
        (by norm_num [cell12600]) (by norm_num [cell12600])
      exact ⟨E.1,E.2.trans (by norm_num [cell12600])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy21 (n := 12600) (by norm_num)
        (q := 1 - (cell12600 ⟨21,by decide⟩).lower)
        (by norm_num [cell12600]) (by norm_num [cell12600])
      exact ⟨E.1,E.2.trans (by norm_num [cell12600])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy22 (n := 12600) (by norm_num)
        (q := 1 - (cell12600 ⟨22,by decide⟩).lower)
        (by norm_num [cell12600]) (by norm_num [cell12600])
      exact ⟨E.1,E.2.trans (by norm_num [cell12600])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy23 (n := 12600) (by norm_num)
        (q := 1 - (cell12600 ⟨23,by decide⟩).lower)
        (by norm_num [cell12600]) (by norm_num [cell12600])
      exact ⟨E.1,E.2.trans (by norm_num [cell12600])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy24 (n := 12600) (by norm_num)
        (q := 1 - (cell12600 ⟨24,by decide⟩).lower)
        (by norm_num [cell12600]) (by norm_num [cell12600])
      exact ⟨E.1,E.2.trans (by norm_num [cell12600])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy25 (n := 12600) (by norm_num)
        (q := 1 - (cell12600 ⟨25,by decide⟩).lower)
        (by norm_num [cell12600]) (by norm_num [cell12600])
      exact ⟨E.1,E.2.trans (by norm_num [cell12600])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy26 (n := 12600) (by norm_num)
        (q := 1 - (cell12600 ⟨26,by decide⟩).lower)
        (by norm_num [cell12600]) (by norm_num [cell12600])
      exact ⟨E.1,E.2.trans (by norm_num [cell12600])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy27 (n := 12600) (by norm_num)
        (q := 1 - (cell12600 ⟨27,by decide⟩).lower)
        (by norm_num [cell12600]) (by norm_num [cell12600])
      exact ⟨E.1,E.2.trans (by norm_num [cell12600])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy28 (n := 12600) (by norm_num)
        (q := 1 - (cell12600 ⟨28,by decide⟩).lower)
        (by norm_num [cell12600]) (by norm_num [cell12600])
      exact ⟨E.1,E.2.trans (by norm_num [cell12600])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy29 (n := 12600) (by norm_num)
        (q := 1 - (cell12600 ⟨29,by decide⟩).lower)
        (by norm_num [cell12600]) (by norm_num [cell12600])
      exact ⟨E.1,E.2.trans (by norm_num [cell12600])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy30 (n := 12600) (by norm_num)
        (q := 1 - (cell12600 ⟨30,by decide⟩).lower)
        (by norm_num [cell12600]) (by norm_num [cell12600])
      exact ⟨E.1,E.2.trans (by norm_num [cell12600])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy31 (n := 12600) (by norm_num)
        (q := 1 - (cell12600 ⟨31,by decide⟩).lower)
        (by norm_num [cell12600]) (by norm_num [cell12600])
      exact ⟨E.1,E.2.trans (by norm_num [cell12600])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy32 (n := 12600) (by norm_num)
        (q := 1 - (cell12600 ⟨32,by decide⟩).lower)
        (by norm_num [cell12600]) (by norm_num [cell12600])
      exact ⟨E.1,E.2.trans (by norm_num [cell12600])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy33 (n := 12600) (by norm_num)
        (q := 1 - (cell12600 ⟨33,by decide⟩).lower)
        (by norm_num [cell12600]) (by norm_num [cell12600])
      exact ⟨E.1,E.2.trans (by norm_num [cell12600])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy34 (n := 12600) (by norm_num)
        (q := 1 - (cell12600 ⟨34,by decide⟩).lower)
        (by norm_num [cell12600]) (by norm_num [cell12600])
      exact ⟨E.1,E.2.trans (by norm_num [cell12600])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy35 (n := 12600) (by norm_num)
        (q := 1 - (cell12600 ⟨35,by decide⟩).lower)
        (by norm_num [cell12600]) (by norm_num [cell12600])
      exact ⟨E.1,E.2.trans (by norm_num [cell12600])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy36 (n := 12600) (by norm_num)
        (q := 1 - (cell12600 ⟨36,by decide⟩).lower)
        (by norm_num [cell12600]) (by norm_num [cell12600])
      exact ⟨E.1,E.2.trans (by norm_num [cell12600])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy37 (n := 12600) (by norm_num)
        (q := 1 - (cell12600 ⟨37,by decide⟩).lower)
        (by norm_num [cell12600]) (by norm_num [cell12600])
      exact ⟨E.1,E.2.trans (by norm_num [cell12600])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy38 (n := 12600) (by norm_num)
        (q := 1 - (cell12600 ⟨38,by decide⟩).lower)
        (by norm_num [cell12600]) (by norm_num [cell12600])
      exact ⟨E.1,E.2.trans (by norm_num [cell12600])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy39 (n := 12600) (by norm_num)
        (q := 1 - (cell12600 ⟨39,by decide⟩).lower)
        (by norm_num [cell12600]) (by norm_num [cell12600])
      exact ⟨E.1,E.2.trans (by norm_num [cell12600])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy40 (n := 12600) (by norm_num)
        (q := 1 - (cell12600 ⟨40,by decide⟩).lower)
        (by norm_num [cell12600]) (by norm_num [cell12600])
      exact ⟨E.1,E.2.trans (by norm_num [cell12600])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy41 (n := 12600) (by norm_num)
        (q := 1 - (cell12600 ⟨41,by decide⟩).lower)
        (by norm_num [cell12600]) (by norm_num [cell12600])
      exact ⟨E.1,E.2.trans (by norm_num [cell12600])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy42 (n := 12600) (by norm_num)
        (q := 1 - (cell12600 ⟨42,by decide⟩).lower)
        (by norm_num [cell12600]) (by norm_num [cell12600])
      exact ⟨E.1,E.2.trans (by norm_num [cell12600])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy43 (n := 12600) (by norm_num)
        (q := 1 - (cell12600 ⟨43,by decide⟩).lower)
        (by norm_num [cell12600]) (by norm_num [cell12600])
      exact ⟨E.1,E.2.trans (by norm_num [cell12600])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy44 (n := 12600) (by norm_num)
        (q := 1 - (cell12600 ⟨44,by decide⟩).lower)
        (by norm_num [cell12600]) (by norm_num [cell12600])
      exact ⟨E.1,E.2.trans (by norm_num [cell12600])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy45 (n := 12600) (by norm_num)
        (q := 1 - (cell12600 ⟨45,by decide⟩).lower)
        (by norm_num [cell12600]) (by norm_num [cell12600])
      exact ⟨E.1,E.2.trans (by norm_num [cell12600])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy46 (n := 12600) (by norm_num)
        (q := 1 - (cell12600 ⟨46,by decide⟩).lower)
        (by norm_num [cell12600]) (by norm_num [cell12600])
      exact ⟨E.1,E.2.trans (by norm_num [cell12600])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy47 (n := 12600) (by norm_num)
        (q := 1 - (cell12600 ⟨47,by decide⟩).lower)
        (by norm_num [cell12600]) (by norm_num [cell12600])
      exact ⟨E.1,E.2.trans (by norm_num [cell12600])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy48 (n := 12600) (by norm_num)
        (q := 1 - (cell12600 ⟨48,by decide⟩).lower)
        (by norm_num [cell12600]) (by norm_num [cell12600])
      exact ⟨E.1,E.2.trans (by norm_num [cell12600])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy49 (n := 12600) (by norm_num)
        (q := 1 - (cell12600 ⟨49,by decide⟩).lower)
        (by norm_num [cell12600]) (by norm_num [cell12600])
      exact ⟨E.1,E.2.trans (by norm_num [cell12600])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy50 (n := 12600) (by norm_num)
        (q := 1 - (cell12600 ⟨50,by decide⟩).lower)
        (by norm_num [cell12600]) (by norm_num [cell12600])
      exact ⟨E.1,E.2.trans (by norm_num [cell12600])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy51 (n := 12600) (by norm_num)
        (q := 1 - (cell12600 ⟨51,by decide⟩).lower)
        (by norm_num [cell12600]) (by norm_num [cell12600])
      exact ⟨E.1,E.2.trans (by norm_num [cell12600])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy52 (n := 12600) (by norm_num)
        (q := 1 - (cell12600 ⟨52,by decide⟩).lower)
        (by norm_num [cell12600]) (by norm_num [cell12600])
      exact ⟨E.1,E.2.trans (by norm_num [cell12600])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12600

/-! Source-cell containment and simple scalar guards at 12600. -/
namespace BstLean.Part269.N12600
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12600)
open BstLean.Part268 (cell12600)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12600 ⟨10,by decide⟩).lower ∧ (cell12600 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12600 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12600 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12600 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12600 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12600 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12600,cell12600,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12600 ⟨11,by decide⟩).lower ∧ (cell12600 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12600 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12600 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12600 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12600 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12600 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12600,cell12600,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12600 ⟨12,by decide⟩).lower ∧ (cell12600 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12600 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12600 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12600 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12600 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12600 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12600,cell12600,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12600 ⟨13,by decide⟩).lower ∧ (cell12600 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12600 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12600 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12600 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12600 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12600 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12600,cell12600,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12600 ⟨14,by decide⟩).lower ∧ (cell12600 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12600 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12600 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12600 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12600 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12600 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12600,cell12600,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12600 ⟨15,by decide⟩).lower ∧ (cell12600 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12600 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12600 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12600 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12600 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12600 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12600,cell12600,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12600 ⟨16,by decide⟩).lower ∧ (cell12600 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12600 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12600 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12600 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12600 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12600 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12600,cell12600,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12600 ⟨17,by decide⟩).lower ∧ (cell12600 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12600 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12600 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12600 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12600 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12600 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12600,cell12600,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12600 ⟨18,by decide⟩).lower ∧ (cell12600 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12600 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12600 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12600 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12600 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12600 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12600,cell12600,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12600 ⟨19,by decide⟩).lower ∧ (cell12600 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12600 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12600 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12600 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12600 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12600 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12600,cell12600,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12600 ⟨20,by decide⟩).lower ∧ (cell12600 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12600 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12600 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12600 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12600 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12600 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12600,cell12600,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12600 ⟨21,by decide⟩).lower ∧ (cell12600 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12600 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12600 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12600 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12600 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12600 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12600,cell12600,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12600 ⟨22,by decide⟩).lower ∧ (cell12600 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12600 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12600 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12600 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12600 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12600 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12600,cell12600,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12600 ⟨23,by decide⟩).lower ∧ (cell12600 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12600 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12600 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12600 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12600 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12600 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12600,cell12600,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12600 ⟨24,by decide⟩).lower ∧ (cell12600 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12600 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12600 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12600 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12600 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12600 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12600,cell12600,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12600 ⟨25,by decide⟩).lower ∧ (cell12600 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12600 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12600 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12600 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12600 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12600 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12600,cell12600,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12600 ⟨26,by decide⟩).lower ∧ (cell12600 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12600 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12600 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12600 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12600 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12600 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12600,cell12600,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12600 ⟨27,by decide⟩).lower ∧ (cell12600 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12600 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12600 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12600 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12600 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12600 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12600,cell12600,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12600 ⟨28,by decide⟩).lower ∧ (cell12600 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12600 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12600 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12600 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12600 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12600 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12600,cell12600,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12600 ⟨29,by decide⟩).lower ∧ (cell12600 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12600 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12600 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12600 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12600 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12600 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12600,cell12600,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12600 ⟨30,by decide⟩).lower ∧ (cell12600 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12600 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12600 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12600 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12600 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12600 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12600,cell12600,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12600 ⟨31,by decide⟩).lower ∧ (cell12600 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12600 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12600 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12600 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12600 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12600 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12600,cell12600,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12600 ⟨32,by decide⟩).lower ∧ (cell12600 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12600 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12600 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12600 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12600 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12600 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12600,cell12600,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12600 ⟨33,by decide⟩).lower ∧ (cell12600 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12600 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12600 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12600 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12600 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12600 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12600,cell12600,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12600 ⟨34,by decide⟩).lower ∧ (cell12600 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12600 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12600 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12600 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12600 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12600 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12600,cell12600,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12600 ⟨35,by decide⟩).lower ∧ (cell12600 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12600 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12600 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12600 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12600 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12600 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12600,cell12600,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12600 ⟨36,by decide⟩).lower ∧ (cell12600 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12600 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12600 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12600 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12600 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12600 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12600,cell12600,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12600 ⟨37,by decide⟩).lower ∧ (cell12600 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12600 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12600 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12600 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12600 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12600 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12600,cell12600,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12600 ⟨38,by decide⟩).lower ∧ (cell12600 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12600 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12600 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12600 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12600 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12600 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12600,cell12600,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12600 ⟨39,by decide⟩).lower ∧ (cell12600 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12600 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12600 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12600 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12600 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12600 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12600,cell12600,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12600 ⟨40,by decide⟩).lower ∧ (cell12600 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12600 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12600 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12600 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12600 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12600 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12600,cell12600,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12600 ⟨41,by decide⟩).lower ∧ (cell12600 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12600 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12600 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12600 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12600 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12600 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12600,cell12600,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12600 ⟨42,by decide⟩).lower ∧ (cell12600 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12600 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12600 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12600 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12600 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12600 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12600,cell12600,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12600 ⟨43,by decide⟩).lower ∧ (cell12600 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12600 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12600 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12600 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12600 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12600 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12600,cell12600,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12600 ⟨44,by decide⟩).lower ∧ (cell12600 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12600 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12600 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12600 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12600 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12600 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12600,cell12600,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12600 ⟨45,by decide⟩).lower ∧ (cell12600 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12600 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12600 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12600 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12600 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12600 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12600,cell12600,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12600 ⟨46,by decide⟩).lower ∧ (cell12600 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12600 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12600 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12600 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12600 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12600 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12600,cell12600,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12600 ⟨47,by decide⟩).lower ∧ (cell12600 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12600 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12600 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12600 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12600 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12600 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12600,cell12600,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12600 ⟨48,by decide⟩).lower ∧ (cell12600 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12600 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12600 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12600 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12600 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12600 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12600,cell12600,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12600 ⟨49,by decide⟩).lower ∧ (cell12600 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12600 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12600 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12600 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12600 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12600 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12600,cell12600,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12600 ⟨50,by decide⟩).lower ∧ (cell12600 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12600 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12600 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12600 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12600 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12600 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12600,cell12600,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12600 ⟨51,by decide⟩).lower ∧ (cell12600 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12600 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12600 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12600 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12600 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12600 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12600,cell12600,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12600 ⟨52,by decide⟩).lower ∧ (cell12600 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12600 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12600 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12600 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12600 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12600 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12600,cell12600,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12600 i).lower ∧
    (cell12600 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12600 i).upper ≤ (0.532 : ℝ) ∧
    (cell12600 i).centre ≤ (0.1 : ℝ) ∧ (cell12600 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12600 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12600 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12600

/-! The local source numeric instances at 12600 have no network premises. -/
namespace BstLean.Part269.N12600
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12600)
open BstLean.Part268 (cell12600)

noncomputable def sourceNumerics12600 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12600 (cell12600 i)
      scalarRow12600.M scalarRow12600.H scalarRow12600.xi := by
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
    energy_allowance := scalarRow12600.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12600]
    centre_nonneg := (scalarRow12600.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D10.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12600])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12600
/-! Actual 12601 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12601
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12601 ≤ (1.035950853383 : ℝ) := by
  have hr : (112.254175868873 : ℝ) ≤ √(12601 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.254175868873 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12601 12601 (11 / 1000) ≤
    (0.008515380836 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12601) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.254175868873 : ℝ) ≤ √(12601 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12601)
  have hdiv : K / √(12601 : ℝ) ≤ K / 112.254175868873 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.254175868873 ≤ (0.008515380836 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12601.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12601 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12601 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12601 := gPlus_lower 12601
end BstLean.Part269.N12601

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12601
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035950853382 : ℝ) ≤ wn 12601 := by
  have hn : √(12601 : ℝ) ≤ 112.254175868874 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12601 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.254175868874 ≤ 2 / √(12601 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000253894488 : ℝ) ≤ rhoBar 12601 BstLean.Part154.csC ∧
    rhoBar 12601 BstLean.Part154.csC ≤ 0.000253894881 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035950853382 : ℝ) / (1.295212 * 12601) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035950853383 : ℝ) / (1.29521 * 12601) := by gcongr
      _ ≤ (0.000253894881 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12601 BstLean.Part154.csC) ≤ 0.001015643987 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12601 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12601 BstLean.Part154.csC) (piBar (rhoBar 12601 BstLean.Part154.csC)) ≤ 0.000193926695 ∧
    cc1 (rhoBar 12601 BstLean.Part154.csC) (piBar (rhoBar 12601 BstLean.Part154.csC)) ≤ 0.000123396829 ∧
    cc2 (rhoBar 12601 BstLean.Part154.csC) ≤ 0.000071632787 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12601 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12601 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12601 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12601 BstLean.Part154.csC * nuR (rhoBar 12601 BstLean.Part154.csC)) ≤ 0.000507805878 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000253894881 : ℝ) * 0.001015643987 := by gcongr
      _ ≤ (0.000507805878 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12601 BstLean.Part154.csC) * nuR (rhoBar 12601 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001015643987 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12601 BstLean.Part154.csC) * rhoBar 12601 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000253894881 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000253894881 / 2 + 0.399 * 0.001015643987 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000193926695 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000507805878 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123396829 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000253894881 / 1.414213562 := by gcongr
      _ ≤ (0.000071632787 : ℝ) := by norm_num

end BstLean.Part269.N12601

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12601
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12601 BstLean.Part154.csC) (piBar (rhoBar 12601 BstLean.Part154.csC)) ≤ 1.62409E-7 := by
  have hr0 : 0 ≤ rhoBar 12601 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12601 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12601 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12601 BstLean.Part154.csC) (piBar (rhoBar 12601 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12601 BstLean.Part154.csC) (piBar (rhoBar 12601 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12601 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000193926695 : ℝ) ^ 2 + 0.000123396829 ^ 2 + 3 * 0.000071632787 ^ 2 +
        2 * 0.797885 * 0.000193926695 * 0.000123396829 + 2 * 0.000193926695 * 0.000071632787 +
        4 * 0.797885 * 0.000123396829 * 0.000071632787 := by gcongr
    _ ≤ (1.62409E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12601 BstLean.Part154.csC Θ ≤ 0.002650671836 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12601 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12601 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12601 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12601 BstLean.Part154.csC) (piBar (rhoBar 12601 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12601 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035950853383 * 1.62409E-7 / (0.000253894488 : ℝ) := by gcongr
    _ ≤ 0.002650671836 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12601 BstLean.Part154.csC Θ ≤ 0.002941465903 + 0.000669781738 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12601 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12601 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12601 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035950853383 : ℝ) * ((2 * Θ * 0.000253894881 +
        (6863 / 10000) * 0.000253894881 * 12601 * 0.001015643987) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002941465903 + 0.000669781738 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12601 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12601 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12601 0.011 Θ ∧ gammaRatio 12601 0.011 Θ ≤ 0.000087282495 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12601 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035950853383 : ℝ) * 0.525 / ((1 - 0.011) * 12601) := by gcongr
      _ ≤ (0.000087282495 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12601 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12601 0.011 Θ) :=
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
    badAllowance 12601 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000676285396 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12601 BstLean.Part154.csC) 1.22 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 2 (rhoBar 12601 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12601 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12601 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12601 0.011 Θ) 1.12 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 1 (gammaRatio 12601 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12601 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12601 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12601 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12601 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035950853383 : ℝ) * 12601 *
        (2.5110E-8 / 1.1045361 + 3.0670E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000676285396 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12601 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003617751299 + 0.003320453574 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12601

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12601
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12601 BstLean.Part154.csC) (piBar (rhoBar 12601 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12601 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12601 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12601 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12601 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12601 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12601 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12601 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12601 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12601 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12601 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12601 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12601 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12601 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12601 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052692321433 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12601) ≤ 0.010638691807 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12601 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035950853383)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010638691807 + 2 * 0.737676 / 12601) := by gcongr
    _ ≤ (0.052692321433 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12601 12 ≤ 0.0015 := by
  exact BstLean.Part269.S10.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12601

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12601
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560499056043 : ℝ) ≤ plow 12601 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12601) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052867589426)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001391602714) : eMP 12601 0.011 xi bn ≤ 0.001197900472 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12601 : ℝ) * (1 - 0.011))) ≤ 0.000592286648 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001391602714 / (12601 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000592286648 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000592286648 : ℝ) + 3.141593 * 0.052867589426 / (12601 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001197900472 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052867589426)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001391602714) : PiBarMP 12601 12 0.011 xi bn ≤ 0.161889564535 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12601 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037304191642 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.635070654342 : ℝ) ≤ √((12601 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.254175868873 : ℝ) ≤ √(12601 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12601) ≤ 0.124114832744 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037304191642 + 0.052867589426 * 1.772454 / (2 * (111.635070654342 : ℝ))) * (1 + 0.001197900472) +
        8 / (12601 * 112.254175868873) + 0.124114832744 := by gcongr
    _ ≤ (0.161889564535 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052867589426)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001391602714) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282621852869) :
    parallelOracle 12601 0.011 xi bn cd ≤ 0.162887910974 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12601 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12601 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560499056043 : ℝ) ≤ plow 12601 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.254175868873 : ℝ) ≤ √(12601 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282621852869 : ℝ) / (2 * 0.560499056043 * 112.254175868873)) * 0.161889564535 +
        0.282621852869 ^ 2 / (2 * 0.560499056043 * 112.254175868873) := by gcongr
    _ ≤ (0.162887910974 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052867589426) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001391602714)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282621852869) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12601 12601 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560499056043 : ℝ) ≤ plow 12601 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.254175868873 : ℝ) ≤ √(12601 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12601 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12601 Θ 1.22 ≤ 0.011813373443 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.254175868873 := by gcongr <;> linarith
      _ ≤ (0.011813373443 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12601 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12601 12601 0.011 ≤ 0.008515380836 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12601 12601 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12601 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12601 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12601 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12601 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162887910974 + 0.011813373443 + (0.008515380836 : ℝ) *
        (1 + 2 * (0.282621852869 + 0.011813373443) / (0.560499056043 * 112.254175868873))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12601]

end BstLean.Part269.N12601

/-! The original eight local profiles supply actual 12601 moment certificates. -/
namespace BstLean.Part269.N12601
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12601 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12601 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12601 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052867589426 ∧
    0 ≤ bN 12601 BstLean.Part154.csC (groupTheta g) ∧ bN 12601 BstLean.Part154.csC (groupTheta g) ≤ 0.001391602714 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12601 12601 0.011
      (momentAllowance 12601 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12601 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12601 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12601 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12601 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12601 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229929531436 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12601 0.011
      (momentAllowance 12601 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12601 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12601
/-! The actual computed-centre upper energy formula at 12601. -/
namespace BstLean.Part269.N12601
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12601

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12601
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12601)
open BstLean.Part268 (cell12601)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085784464614
  | 2 => 0.086732745833
  | 3 => 0.087679993960
  | 4 => 0.088627816141
  | 5 => 0.089578149802
  | 6 => 0.090533310854
  | 7 => 0.091496046282
  | 8 => 0.092469591117
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12601 12601 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12601 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12601

/-! Actual upper energy certificates on all 43 source endpoints at 12601. -/
namespace BstLean.Part269.N12601
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12601)
open BstLean.Part268 (cell12601)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12601 (gMinus 12601) (1 - (cell12601 i).lower) ≤ 1 ∧
    energyUpper 12601 (gMinus 12601) (BstLean.Part211.gPlus 12601)
      (finiteEnergy 12601 12601 0.011) (1 - (cell12601 i).lower) ≤
      (cell12601 i).energy := by
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
      have E := BstLean.Part269.S10.uniformEnergy10 (n := 12601) (by norm_num)
        (q := 1 - (cell12601 ⟨10,by decide⟩).lower)
        (by norm_num [cell12601]) (by norm_num [cell12601])
      exact ⟨E.1,E.2.trans (by norm_num [cell12601])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy11 (n := 12601) (by norm_num)
        (q := 1 - (cell12601 ⟨11,by decide⟩).lower)
        (by norm_num [cell12601]) (by norm_num [cell12601])
      exact ⟨E.1,E.2.trans (by norm_num [cell12601])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy12 (n := 12601) (by norm_num)
        (q := 1 - (cell12601 ⟨12,by decide⟩).lower)
        (by norm_num [cell12601]) (by norm_num [cell12601])
      exact ⟨E.1,E.2.trans (by norm_num [cell12601])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy13 (n := 12601) (by norm_num)
        (q := 1 - (cell12601 ⟨13,by decide⟩).lower)
        (by norm_num [cell12601]) (by norm_num [cell12601])
      exact ⟨E.1,E.2.trans (by norm_num [cell12601])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy14 (n := 12601) (by norm_num)
        (q := 1 - (cell12601 ⟨14,by decide⟩).lower)
        (by norm_num [cell12601]) (by norm_num [cell12601])
      exact ⟨E.1,E.2.trans (by norm_num [cell12601])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy15 (n := 12601) (by norm_num)
        (q := 1 - (cell12601 ⟨15,by decide⟩).lower)
        (by norm_num [cell12601]) (by norm_num [cell12601])
      exact ⟨E.1,E.2.trans (by norm_num [cell12601])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy16 (n := 12601) (by norm_num)
        (q := 1 - (cell12601 ⟨16,by decide⟩).lower)
        (by norm_num [cell12601]) (by norm_num [cell12601])
      exact ⟨E.1,E.2.trans (by norm_num [cell12601])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy17 (n := 12601) (by norm_num)
        (q := 1 - (cell12601 ⟨17,by decide⟩).lower)
        (by norm_num [cell12601]) (by norm_num [cell12601])
      exact ⟨E.1,E.2.trans (by norm_num [cell12601])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy18 (n := 12601) (by norm_num)
        (q := 1 - (cell12601 ⟨18,by decide⟩).lower)
        (by norm_num [cell12601]) (by norm_num [cell12601])
      exact ⟨E.1,E.2.trans (by norm_num [cell12601])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy19 (n := 12601) (by norm_num)
        (q := 1 - (cell12601 ⟨19,by decide⟩).lower)
        (by norm_num [cell12601]) (by norm_num [cell12601])
      exact ⟨E.1,E.2.trans (by norm_num [cell12601])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy20 (n := 12601) (by norm_num)
        (q := 1 - (cell12601 ⟨20,by decide⟩).lower)
        (by norm_num [cell12601]) (by norm_num [cell12601])
      exact ⟨E.1,E.2.trans (by norm_num [cell12601])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy21 (n := 12601) (by norm_num)
        (q := 1 - (cell12601 ⟨21,by decide⟩).lower)
        (by norm_num [cell12601]) (by norm_num [cell12601])
      exact ⟨E.1,E.2.trans (by norm_num [cell12601])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy22 (n := 12601) (by norm_num)
        (q := 1 - (cell12601 ⟨22,by decide⟩).lower)
        (by norm_num [cell12601]) (by norm_num [cell12601])
      exact ⟨E.1,E.2.trans (by norm_num [cell12601])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy23 (n := 12601) (by norm_num)
        (q := 1 - (cell12601 ⟨23,by decide⟩).lower)
        (by norm_num [cell12601]) (by norm_num [cell12601])
      exact ⟨E.1,E.2.trans (by norm_num [cell12601])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy24 (n := 12601) (by norm_num)
        (q := 1 - (cell12601 ⟨24,by decide⟩).lower)
        (by norm_num [cell12601]) (by norm_num [cell12601])
      exact ⟨E.1,E.2.trans (by norm_num [cell12601])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy25 (n := 12601) (by norm_num)
        (q := 1 - (cell12601 ⟨25,by decide⟩).lower)
        (by norm_num [cell12601]) (by norm_num [cell12601])
      exact ⟨E.1,E.2.trans (by norm_num [cell12601])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy26 (n := 12601) (by norm_num)
        (q := 1 - (cell12601 ⟨26,by decide⟩).lower)
        (by norm_num [cell12601]) (by norm_num [cell12601])
      exact ⟨E.1,E.2.trans (by norm_num [cell12601])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy27 (n := 12601) (by norm_num)
        (q := 1 - (cell12601 ⟨27,by decide⟩).lower)
        (by norm_num [cell12601]) (by norm_num [cell12601])
      exact ⟨E.1,E.2.trans (by norm_num [cell12601])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy28 (n := 12601) (by norm_num)
        (q := 1 - (cell12601 ⟨28,by decide⟩).lower)
        (by norm_num [cell12601]) (by norm_num [cell12601])
      exact ⟨E.1,E.2.trans (by norm_num [cell12601])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy29 (n := 12601) (by norm_num)
        (q := 1 - (cell12601 ⟨29,by decide⟩).lower)
        (by norm_num [cell12601]) (by norm_num [cell12601])
      exact ⟨E.1,E.2.trans (by norm_num [cell12601])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy30 (n := 12601) (by norm_num)
        (q := 1 - (cell12601 ⟨30,by decide⟩).lower)
        (by norm_num [cell12601]) (by norm_num [cell12601])
      exact ⟨E.1,E.2.trans (by norm_num [cell12601])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy31 (n := 12601) (by norm_num)
        (q := 1 - (cell12601 ⟨31,by decide⟩).lower)
        (by norm_num [cell12601]) (by norm_num [cell12601])
      exact ⟨E.1,E.2.trans (by norm_num [cell12601])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy32 (n := 12601) (by norm_num)
        (q := 1 - (cell12601 ⟨32,by decide⟩).lower)
        (by norm_num [cell12601]) (by norm_num [cell12601])
      exact ⟨E.1,E.2.trans (by norm_num [cell12601])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy33 (n := 12601) (by norm_num)
        (q := 1 - (cell12601 ⟨33,by decide⟩).lower)
        (by norm_num [cell12601]) (by norm_num [cell12601])
      exact ⟨E.1,E.2.trans (by norm_num [cell12601])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy34 (n := 12601) (by norm_num)
        (q := 1 - (cell12601 ⟨34,by decide⟩).lower)
        (by norm_num [cell12601]) (by norm_num [cell12601])
      exact ⟨E.1,E.2.trans (by norm_num [cell12601])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy35 (n := 12601) (by norm_num)
        (q := 1 - (cell12601 ⟨35,by decide⟩).lower)
        (by norm_num [cell12601]) (by norm_num [cell12601])
      exact ⟨E.1,E.2.trans (by norm_num [cell12601])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy36 (n := 12601) (by norm_num)
        (q := 1 - (cell12601 ⟨36,by decide⟩).lower)
        (by norm_num [cell12601]) (by norm_num [cell12601])
      exact ⟨E.1,E.2.trans (by norm_num [cell12601])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy37 (n := 12601) (by norm_num)
        (q := 1 - (cell12601 ⟨37,by decide⟩).lower)
        (by norm_num [cell12601]) (by norm_num [cell12601])
      exact ⟨E.1,E.2.trans (by norm_num [cell12601])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy38 (n := 12601) (by norm_num)
        (q := 1 - (cell12601 ⟨38,by decide⟩).lower)
        (by norm_num [cell12601]) (by norm_num [cell12601])
      exact ⟨E.1,E.2.trans (by norm_num [cell12601])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy39 (n := 12601) (by norm_num)
        (q := 1 - (cell12601 ⟨39,by decide⟩).lower)
        (by norm_num [cell12601]) (by norm_num [cell12601])
      exact ⟨E.1,E.2.trans (by norm_num [cell12601])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy40 (n := 12601) (by norm_num)
        (q := 1 - (cell12601 ⟨40,by decide⟩).lower)
        (by norm_num [cell12601]) (by norm_num [cell12601])
      exact ⟨E.1,E.2.trans (by norm_num [cell12601])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy41 (n := 12601) (by norm_num)
        (q := 1 - (cell12601 ⟨41,by decide⟩).lower)
        (by norm_num [cell12601]) (by norm_num [cell12601])
      exact ⟨E.1,E.2.trans (by norm_num [cell12601])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy42 (n := 12601) (by norm_num)
        (q := 1 - (cell12601 ⟨42,by decide⟩).lower)
        (by norm_num [cell12601]) (by norm_num [cell12601])
      exact ⟨E.1,E.2.trans (by norm_num [cell12601])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy43 (n := 12601) (by norm_num)
        (q := 1 - (cell12601 ⟨43,by decide⟩).lower)
        (by norm_num [cell12601]) (by norm_num [cell12601])
      exact ⟨E.1,E.2.trans (by norm_num [cell12601])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy44 (n := 12601) (by norm_num)
        (q := 1 - (cell12601 ⟨44,by decide⟩).lower)
        (by norm_num [cell12601]) (by norm_num [cell12601])
      exact ⟨E.1,E.2.trans (by norm_num [cell12601])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy45 (n := 12601) (by norm_num)
        (q := 1 - (cell12601 ⟨45,by decide⟩).lower)
        (by norm_num [cell12601]) (by norm_num [cell12601])
      exact ⟨E.1,E.2.trans (by norm_num [cell12601])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy46 (n := 12601) (by norm_num)
        (q := 1 - (cell12601 ⟨46,by decide⟩).lower)
        (by norm_num [cell12601]) (by norm_num [cell12601])
      exact ⟨E.1,E.2.trans (by norm_num [cell12601])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy47 (n := 12601) (by norm_num)
        (q := 1 - (cell12601 ⟨47,by decide⟩).lower)
        (by norm_num [cell12601]) (by norm_num [cell12601])
      exact ⟨E.1,E.2.trans (by norm_num [cell12601])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy48 (n := 12601) (by norm_num)
        (q := 1 - (cell12601 ⟨48,by decide⟩).lower)
        (by norm_num [cell12601]) (by norm_num [cell12601])
      exact ⟨E.1,E.2.trans (by norm_num [cell12601])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy49 (n := 12601) (by norm_num)
        (q := 1 - (cell12601 ⟨49,by decide⟩).lower)
        (by norm_num [cell12601]) (by norm_num [cell12601])
      exact ⟨E.1,E.2.trans (by norm_num [cell12601])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy50 (n := 12601) (by norm_num)
        (q := 1 - (cell12601 ⟨50,by decide⟩).lower)
        (by norm_num [cell12601]) (by norm_num [cell12601])
      exact ⟨E.1,E.2.trans (by norm_num [cell12601])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy51 (n := 12601) (by norm_num)
        (q := 1 - (cell12601 ⟨51,by decide⟩).lower)
        (by norm_num [cell12601]) (by norm_num [cell12601])
      exact ⟨E.1,E.2.trans (by norm_num [cell12601])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy52 (n := 12601) (by norm_num)
        (q := 1 - (cell12601 ⟨52,by decide⟩).lower)
        (by norm_num [cell12601]) (by norm_num [cell12601])
      exact ⟨E.1,E.2.trans (by norm_num [cell12601])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12601

/-! Source-cell containment and simple scalar guards at 12601. -/
namespace BstLean.Part269.N12601
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12601)
open BstLean.Part268 (cell12601)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12601 ⟨10,by decide⟩).lower ∧ (cell12601 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12601 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12601 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12601 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12601 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12601 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12601,cell12601,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12601 ⟨11,by decide⟩).lower ∧ (cell12601 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12601 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12601 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12601 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12601 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12601 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12601,cell12601,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12601 ⟨12,by decide⟩).lower ∧ (cell12601 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12601 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12601 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12601 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12601 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12601 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12601,cell12601,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12601 ⟨13,by decide⟩).lower ∧ (cell12601 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12601 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12601 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12601 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12601 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12601 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12601,cell12601,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12601 ⟨14,by decide⟩).lower ∧ (cell12601 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12601 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12601 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12601 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12601 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12601 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12601,cell12601,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12601 ⟨15,by decide⟩).lower ∧ (cell12601 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12601 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12601 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12601 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12601 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12601 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12601,cell12601,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12601 ⟨16,by decide⟩).lower ∧ (cell12601 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12601 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12601 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12601 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12601 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12601 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12601,cell12601,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12601 ⟨17,by decide⟩).lower ∧ (cell12601 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12601 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12601 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12601 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12601 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12601 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12601,cell12601,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12601 ⟨18,by decide⟩).lower ∧ (cell12601 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12601 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12601 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12601 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12601 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12601 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12601,cell12601,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12601 ⟨19,by decide⟩).lower ∧ (cell12601 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12601 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12601 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12601 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12601 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12601 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12601,cell12601,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12601 ⟨20,by decide⟩).lower ∧ (cell12601 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12601 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12601 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12601 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12601 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12601 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12601,cell12601,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12601 ⟨21,by decide⟩).lower ∧ (cell12601 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12601 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12601 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12601 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12601 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12601 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12601,cell12601,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12601 ⟨22,by decide⟩).lower ∧ (cell12601 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12601 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12601 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12601 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12601 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12601 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12601,cell12601,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12601 ⟨23,by decide⟩).lower ∧ (cell12601 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12601 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12601 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12601 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12601 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12601 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12601,cell12601,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12601 ⟨24,by decide⟩).lower ∧ (cell12601 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12601 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12601 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12601 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12601 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12601 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12601,cell12601,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12601 ⟨25,by decide⟩).lower ∧ (cell12601 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12601 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12601 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12601 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12601 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12601 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12601,cell12601,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12601 ⟨26,by decide⟩).lower ∧ (cell12601 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12601 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12601 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12601 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12601 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12601 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12601,cell12601,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12601 ⟨27,by decide⟩).lower ∧ (cell12601 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12601 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12601 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12601 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12601 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12601 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12601,cell12601,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12601 ⟨28,by decide⟩).lower ∧ (cell12601 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12601 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12601 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12601 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12601 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12601 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12601,cell12601,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12601 ⟨29,by decide⟩).lower ∧ (cell12601 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12601 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12601 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12601 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12601 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12601 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12601,cell12601,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12601 ⟨30,by decide⟩).lower ∧ (cell12601 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12601 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12601 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12601 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12601 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12601 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12601,cell12601,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12601 ⟨31,by decide⟩).lower ∧ (cell12601 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12601 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12601 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12601 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12601 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12601 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12601,cell12601,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12601 ⟨32,by decide⟩).lower ∧ (cell12601 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12601 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12601 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12601 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12601 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12601 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12601,cell12601,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12601 ⟨33,by decide⟩).lower ∧ (cell12601 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12601 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12601 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12601 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12601 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12601 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12601,cell12601,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12601 ⟨34,by decide⟩).lower ∧ (cell12601 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12601 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12601 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12601 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12601 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12601 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12601,cell12601,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12601 ⟨35,by decide⟩).lower ∧ (cell12601 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12601 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12601 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12601 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12601 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12601 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12601,cell12601,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12601 ⟨36,by decide⟩).lower ∧ (cell12601 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12601 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12601 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12601 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12601 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12601 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12601,cell12601,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12601 ⟨37,by decide⟩).lower ∧ (cell12601 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12601 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12601 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12601 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12601 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12601 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12601,cell12601,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12601 ⟨38,by decide⟩).lower ∧ (cell12601 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12601 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12601 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12601 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12601 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12601 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12601,cell12601,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12601 ⟨39,by decide⟩).lower ∧ (cell12601 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12601 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12601 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12601 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12601 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12601 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12601,cell12601,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12601 ⟨40,by decide⟩).lower ∧ (cell12601 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12601 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12601 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12601 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12601 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12601 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12601,cell12601,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12601 ⟨41,by decide⟩).lower ∧ (cell12601 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12601 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12601 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12601 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12601 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12601 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12601,cell12601,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12601 ⟨42,by decide⟩).lower ∧ (cell12601 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12601 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12601 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12601 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12601 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12601 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12601,cell12601,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12601 ⟨43,by decide⟩).lower ∧ (cell12601 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12601 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12601 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12601 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12601 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12601 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12601,cell12601,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12601 ⟨44,by decide⟩).lower ∧ (cell12601 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12601 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12601 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12601 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12601 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12601 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12601,cell12601,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12601 ⟨45,by decide⟩).lower ∧ (cell12601 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12601 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12601 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12601 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12601 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12601 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12601,cell12601,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12601 ⟨46,by decide⟩).lower ∧ (cell12601 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12601 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12601 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12601 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12601 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12601 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12601,cell12601,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12601 ⟨47,by decide⟩).lower ∧ (cell12601 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12601 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12601 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12601 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12601 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12601 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12601,cell12601,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12601 ⟨48,by decide⟩).lower ∧ (cell12601 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12601 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12601 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12601 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12601 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12601 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12601,cell12601,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12601 ⟨49,by decide⟩).lower ∧ (cell12601 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12601 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12601 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12601 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12601 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12601 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12601,cell12601,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12601 ⟨50,by decide⟩).lower ∧ (cell12601 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12601 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12601 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12601 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12601 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12601 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12601,cell12601,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12601 ⟨51,by decide⟩).lower ∧ (cell12601 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12601 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12601 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12601 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12601 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12601 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12601,cell12601,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12601 ⟨52,by decide⟩).lower ∧ (cell12601 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12601 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12601 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12601 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12601 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12601 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12601,cell12601,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12601 i).lower ∧
    (cell12601 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12601 i).upper ≤ (0.532 : ℝ) ∧
    (cell12601 i).centre ≤ (0.1 : ℝ) ∧ (cell12601 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12601 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12601 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12601

/-! The local source numeric instances at 12601 have no network premises. -/
namespace BstLean.Part269.N12601
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12601)
open BstLean.Part268 (cell12601)

noncomputable def sourceNumerics12601 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12601 (cell12601 i)
      scalarRow12601.M scalarRow12601.H scalarRow12601.xi := by
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
    energy_allowance := scalarRow12601.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12601]
    centre_nonneg := (scalarRow12601.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D10.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12601])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12601
/-! Actual 12602 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12602
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12602 ≤ (1.035949414366 : ℝ) := by
  have hr : (112.258629957789 : ℝ) ≤ √(12602 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.258629957789 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12602 12602 (11 / 1000) ≤
    (0.008515042969 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12602) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.258629957789 : ℝ) ≤ √(12602 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12602)
  have hdiv : K / √(12602 : ℝ) ≤ K / 112.258629957789 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.258629957789 ≤ (0.008515042969 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12602.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12602 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12602 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12602 := gPlus_lower 12602
end BstLean.Part269.N12602

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12602
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035949414365 : ℝ) ≤ wn 12602 := by
  have hn : √(12602 : ℝ) ≤ 112.258629957790 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12602 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.258629957790 ≤ 2 / √(12602 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000253873988 : ℝ) ≤ rhoBar 12602 BstLean.Part154.csC ∧
    rhoBar 12602 BstLean.Part154.csC ≤ 0.000253874381 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035949414365 : ℝ) / (1.295212 * 12602) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035949414366 : ℝ) / (1.29521 * 12602) := by gcongr
      _ ≤ (0.000253874381 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12602 BstLean.Part154.csC) ≤ 0.001015561977 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12602 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12602 BstLean.Part154.csC) (piBar (rhoBar 12602 BstLean.Part154.csC)) ≤ 0.000193911036 ∧
    cc1 (rhoBar 12602 BstLean.Part154.csC) (piBar (rhoBar 12602 BstLean.Part154.csC)) ≤ 0.000123386865 ∧
    cc2 (rhoBar 12602 BstLean.Part154.csC) ≤ 0.000071627003 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12602 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12602 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12602 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12602 BstLean.Part154.csC * nuR (rhoBar 12602 BstLean.Part154.csC)) ≤ 0.000507764875 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000253874381 : ℝ) * 0.001015561977 := by gcongr
      _ ≤ (0.000507764875 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12602 BstLean.Part154.csC) * nuR (rhoBar 12602 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001015561977 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12602 BstLean.Part154.csC) * rhoBar 12602 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000253874381 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000253874381 / 2 + 0.399 * 0.001015561977 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000193911036 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000507764875 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123386865 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000253874381 / 1.414213562 := by gcongr
      _ ≤ (0.000071627003 : ℝ) := by norm_num

end BstLean.Part269.N12602

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12602
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12602 BstLean.Part154.csC) (piBar (rhoBar 12602 BstLean.Part154.csC)) ≤ 1.62383E-7 := by
  have hr0 : 0 ≤ rhoBar 12602 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12602 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12602 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12602 BstLean.Part154.csC) (piBar (rhoBar 12602 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12602 BstLean.Part154.csC) (piBar (rhoBar 12602 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12602 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000193911036 : ℝ) ^ 2 + 0.000123386865 ^ 2 + 3 * 0.000071627003 ^ 2 +
        2 * 0.797885 * 0.000193911036 * 0.000123386865 + 2 * 0.000193911036 * 0.000071627003 +
        4 * 0.797885 * 0.000123386865 * 0.000071627003 := by gcongr
    _ ≤ (1.62383E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12602 BstLean.Part154.csC Θ ≤ 0.002650457813 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12602 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12602 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12602 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12602 BstLean.Part154.csC) (piBar (rhoBar 12602 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12602 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035949414366 * 1.62383E-7 / (0.000253873988 : ℝ) := by gcongr
    _ ≤ 0.002650457813 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12602 BstLean.Part154.csC Θ ≤ 0.002941220216 + 0.000669726728 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12602 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12602 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12602 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035949414366 : ℝ) * ((2 * Θ * 0.000253874381 +
        (6863 / 10000) * 0.000253874381 * 12602 * 0.001015561977) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002941220216 + 0.000669726728 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12602 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12602 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12602 0.011 Θ ∧ gammaRatio 12602 0.011 Θ ≤ 0.000087275447 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12602 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035949414366 : ℝ) * 0.525 / ((1 - 0.011) * 12602) := by gcongr
      _ ≤ (0.000087275447 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12602 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12602 0.011 Θ) :=
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
    badAllowance 12602 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000676285396 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12602 BstLean.Part154.csC) 1.22 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 2 (rhoBar 12602 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12602 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12602 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12602 0.011 Θ) 1.12 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 1 (gammaRatio 12602 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12602 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12602 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12602 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12602 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035949414366 : ℝ) * 12602 *
        (2.5110E-8 / 1.1045361 + 3.0670E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000676285396 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12602 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003617505612 + 0.003320184541 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12602

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12602
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12602 BstLean.Part154.csC) (piBar (rhoBar 12602 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12602 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12602 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12602 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12602 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12602 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12602 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12602 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12602 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12602 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12602 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12602 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12602 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12602 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12602 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052690208000 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12602) ≤ 0.010638269695 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12602 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035949414366)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010638269695 + 2 * 0.737676 / 12602) := by gcongr
    _ ≤ (0.052690208000 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12602 12 ≤ 0.0015 := by
  exact BstLean.Part269.S10.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12602

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12602
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560499101975 : ℝ) ≤ plow 12602 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12602) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052867202497)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001391490352) : eMP 12602 0.011 xi bn ≤ 0.001197804495 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12602 : ℝ) * (1 - 0.011))) ≤ 0.000592239237 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001391490352 / (12602 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000592239237 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000592239237 : ℝ) + 3.141593 * 0.052867202497 / (12602 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001197804495 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052867202497)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001391490352) : PiBarMP 12602 12 0.011 xi bn ≤ 0.161883108127 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12602 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037302685587 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.639500178028 : ℝ) ≤ √((12602 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.258629957789 : ℝ) ≤ √(12602 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12602) ≤ 0.124109908236 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037302685587 + 0.052867202497 * 1.772454 / (2 * (111.639500178028 : ℝ))) * (1 + 0.001197804495) +
        8 / (12602 * 112.258629957789) + 0.124109908236 := by gcongr
    _ ≤ (0.161883108127 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052867202497)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001391490352) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282618898026) :
    parallelOracle 12602 0.011 xi bn cd ≤ 0.162881383299 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12602 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12602 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560499101975 : ℝ) ≤ plow 12602 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.258629957789 : ℝ) ≤ √(12602 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282618898026 : ℝ) / (2 * 0.560499101975 * 112.258629957789)) * 0.161883108127 +
        0.282618898026 ^ 2 / (2 * 0.560499101975 * 112.258629957789) := by gcongr
    _ ≤ (0.162881383299 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052867202497) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001391490352)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282618898026) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12602 12602 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560499101975 : ℝ) ≤ plow 12602 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.258629957789 : ℝ) ≤ √(12602 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12602 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12602 Θ 1.22 ≤ 0.011812904723 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.258629957789 := by gcongr <;> linarith
      _ ≤ (0.011812904723 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12602 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12602 12602 0.011 ≤ 0.008515042969 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12602 12602 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12602 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12602 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12602 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12602 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162881383299 + 0.011812904723 + (0.008515042969 : ℝ) *
        (1 + 2 * (0.282618898026 + 0.011812904723) / (0.560499101975 * 112.258629957789))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12602]

end BstLean.Part269.N12602

/-! The original eight local profiles supply actual 12602 moment certificates. -/
namespace BstLean.Part269.N12602
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12602 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12602 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12602 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052867202497 ∧
    0 ≤ bN 12602 BstLean.Part154.csC (groupTheta g) ∧ bN 12602 BstLean.Part154.csC (groupTheta g) ≤ 0.001391490352 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12602 12602 0.011
      (momentAllowance 12602 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12602 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12602 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12602 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12602 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12602 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229928690026 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12602 0.011
      (momentAllowance 12602 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12602 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12602
/-! The actual computed-centre upper energy formula at 12602. -/
namespace BstLean.Part269.N12602
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12602

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12602
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12602)
open BstLean.Part268 (cell12602)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085781435991
  | 2 => 0.086729658957
  | 3 => 0.087676839917
  | 4 => 0.088624583994
  | 5 => 0.089574826240
  | 6 => 0.090529879801
  | 7 => 0.091492488451
  | 8 => 0.092465883530
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12602 12602 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12602 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12602

/-! Actual upper energy certificates on all 43 source endpoints at 12602. -/
namespace BstLean.Part269.N12602
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12602)
open BstLean.Part268 (cell12602)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12602 (gMinus 12602) (1 - (cell12602 i).lower) ≤ 1 ∧
    energyUpper 12602 (gMinus 12602) (BstLean.Part211.gPlus 12602)
      (finiteEnergy 12602 12602 0.011) (1 - (cell12602 i).lower) ≤
      (cell12602 i).energy := by
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
      have E := BstLean.Part269.S10.uniformEnergy10 (n := 12602) (by norm_num)
        (q := 1 - (cell12602 ⟨10,by decide⟩).lower)
        (by norm_num [cell12602]) (by norm_num [cell12602])
      exact ⟨E.1,E.2.trans (by norm_num [cell12602])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy11 (n := 12602) (by norm_num)
        (q := 1 - (cell12602 ⟨11,by decide⟩).lower)
        (by norm_num [cell12602]) (by norm_num [cell12602])
      exact ⟨E.1,E.2.trans (by norm_num [cell12602])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy12 (n := 12602) (by norm_num)
        (q := 1 - (cell12602 ⟨12,by decide⟩).lower)
        (by norm_num [cell12602]) (by norm_num [cell12602])
      exact ⟨E.1,E.2.trans (by norm_num [cell12602])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy13 (n := 12602) (by norm_num)
        (q := 1 - (cell12602 ⟨13,by decide⟩).lower)
        (by norm_num [cell12602]) (by norm_num [cell12602])
      exact ⟨E.1,E.2.trans (by norm_num [cell12602])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy14 (n := 12602) (by norm_num)
        (q := 1 - (cell12602 ⟨14,by decide⟩).lower)
        (by norm_num [cell12602]) (by norm_num [cell12602])
      exact ⟨E.1,E.2.trans (by norm_num [cell12602])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy15 (n := 12602) (by norm_num)
        (q := 1 - (cell12602 ⟨15,by decide⟩).lower)
        (by norm_num [cell12602]) (by norm_num [cell12602])
      exact ⟨E.1,E.2.trans (by norm_num [cell12602])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy16 (n := 12602) (by norm_num)
        (q := 1 - (cell12602 ⟨16,by decide⟩).lower)
        (by norm_num [cell12602]) (by norm_num [cell12602])
      exact ⟨E.1,E.2.trans (by norm_num [cell12602])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy17 (n := 12602) (by norm_num)
        (q := 1 - (cell12602 ⟨17,by decide⟩).lower)
        (by norm_num [cell12602]) (by norm_num [cell12602])
      exact ⟨E.1,E.2.trans (by norm_num [cell12602])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy18 (n := 12602) (by norm_num)
        (q := 1 - (cell12602 ⟨18,by decide⟩).lower)
        (by norm_num [cell12602]) (by norm_num [cell12602])
      exact ⟨E.1,E.2.trans (by norm_num [cell12602])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy19 (n := 12602) (by norm_num)
        (q := 1 - (cell12602 ⟨19,by decide⟩).lower)
        (by norm_num [cell12602]) (by norm_num [cell12602])
      exact ⟨E.1,E.2.trans (by norm_num [cell12602])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy20 (n := 12602) (by norm_num)
        (q := 1 - (cell12602 ⟨20,by decide⟩).lower)
        (by norm_num [cell12602]) (by norm_num [cell12602])
      exact ⟨E.1,E.2.trans (by norm_num [cell12602])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy21 (n := 12602) (by norm_num)
        (q := 1 - (cell12602 ⟨21,by decide⟩).lower)
        (by norm_num [cell12602]) (by norm_num [cell12602])
      exact ⟨E.1,E.2.trans (by norm_num [cell12602])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy22 (n := 12602) (by norm_num)
        (q := 1 - (cell12602 ⟨22,by decide⟩).lower)
        (by norm_num [cell12602]) (by norm_num [cell12602])
      exact ⟨E.1,E.2.trans (by norm_num [cell12602])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy23 (n := 12602) (by norm_num)
        (q := 1 - (cell12602 ⟨23,by decide⟩).lower)
        (by norm_num [cell12602]) (by norm_num [cell12602])
      exact ⟨E.1,E.2.trans (by norm_num [cell12602])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy24 (n := 12602) (by norm_num)
        (q := 1 - (cell12602 ⟨24,by decide⟩).lower)
        (by norm_num [cell12602]) (by norm_num [cell12602])
      exact ⟨E.1,E.2.trans (by norm_num [cell12602])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy25 (n := 12602) (by norm_num)
        (q := 1 - (cell12602 ⟨25,by decide⟩).lower)
        (by norm_num [cell12602]) (by norm_num [cell12602])
      exact ⟨E.1,E.2.trans (by norm_num [cell12602])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy26 (n := 12602) (by norm_num)
        (q := 1 - (cell12602 ⟨26,by decide⟩).lower)
        (by norm_num [cell12602]) (by norm_num [cell12602])
      exact ⟨E.1,E.2.trans (by norm_num [cell12602])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy27 (n := 12602) (by norm_num)
        (q := 1 - (cell12602 ⟨27,by decide⟩).lower)
        (by norm_num [cell12602]) (by norm_num [cell12602])
      exact ⟨E.1,E.2.trans (by norm_num [cell12602])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy28 (n := 12602) (by norm_num)
        (q := 1 - (cell12602 ⟨28,by decide⟩).lower)
        (by norm_num [cell12602]) (by norm_num [cell12602])
      exact ⟨E.1,E.2.trans (by norm_num [cell12602])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy29 (n := 12602) (by norm_num)
        (q := 1 - (cell12602 ⟨29,by decide⟩).lower)
        (by norm_num [cell12602]) (by norm_num [cell12602])
      exact ⟨E.1,E.2.trans (by norm_num [cell12602])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy30 (n := 12602) (by norm_num)
        (q := 1 - (cell12602 ⟨30,by decide⟩).lower)
        (by norm_num [cell12602]) (by norm_num [cell12602])
      exact ⟨E.1,E.2.trans (by norm_num [cell12602])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy31 (n := 12602) (by norm_num)
        (q := 1 - (cell12602 ⟨31,by decide⟩).lower)
        (by norm_num [cell12602]) (by norm_num [cell12602])
      exact ⟨E.1,E.2.trans (by norm_num [cell12602])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy32 (n := 12602) (by norm_num)
        (q := 1 - (cell12602 ⟨32,by decide⟩).lower)
        (by norm_num [cell12602]) (by norm_num [cell12602])
      exact ⟨E.1,E.2.trans (by norm_num [cell12602])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy33 (n := 12602) (by norm_num)
        (q := 1 - (cell12602 ⟨33,by decide⟩).lower)
        (by norm_num [cell12602]) (by norm_num [cell12602])
      exact ⟨E.1,E.2.trans (by norm_num [cell12602])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy34 (n := 12602) (by norm_num)
        (q := 1 - (cell12602 ⟨34,by decide⟩).lower)
        (by norm_num [cell12602]) (by norm_num [cell12602])
      exact ⟨E.1,E.2.trans (by norm_num [cell12602])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy35 (n := 12602) (by norm_num)
        (q := 1 - (cell12602 ⟨35,by decide⟩).lower)
        (by norm_num [cell12602]) (by norm_num [cell12602])
      exact ⟨E.1,E.2.trans (by norm_num [cell12602])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy36 (n := 12602) (by norm_num)
        (q := 1 - (cell12602 ⟨36,by decide⟩).lower)
        (by norm_num [cell12602]) (by norm_num [cell12602])
      exact ⟨E.1,E.2.trans (by norm_num [cell12602])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy37 (n := 12602) (by norm_num)
        (q := 1 - (cell12602 ⟨37,by decide⟩).lower)
        (by norm_num [cell12602]) (by norm_num [cell12602])
      exact ⟨E.1,E.2.trans (by norm_num [cell12602])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy38 (n := 12602) (by norm_num)
        (q := 1 - (cell12602 ⟨38,by decide⟩).lower)
        (by norm_num [cell12602]) (by norm_num [cell12602])
      exact ⟨E.1,E.2.trans (by norm_num [cell12602])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy39 (n := 12602) (by norm_num)
        (q := 1 - (cell12602 ⟨39,by decide⟩).lower)
        (by norm_num [cell12602]) (by norm_num [cell12602])
      exact ⟨E.1,E.2.trans (by norm_num [cell12602])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy40 (n := 12602) (by norm_num)
        (q := 1 - (cell12602 ⟨40,by decide⟩).lower)
        (by norm_num [cell12602]) (by norm_num [cell12602])
      exact ⟨E.1,E.2.trans (by norm_num [cell12602])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy41 (n := 12602) (by norm_num)
        (q := 1 - (cell12602 ⟨41,by decide⟩).lower)
        (by norm_num [cell12602]) (by norm_num [cell12602])
      exact ⟨E.1,E.2.trans (by norm_num [cell12602])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy42 (n := 12602) (by norm_num)
        (q := 1 - (cell12602 ⟨42,by decide⟩).lower)
        (by norm_num [cell12602]) (by norm_num [cell12602])
      exact ⟨E.1,E.2.trans (by norm_num [cell12602])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy43 (n := 12602) (by norm_num)
        (q := 1 - (cell12602 ⟨43,by decide⟩).lower)
        (by norm_num [cell12602]) (by norm_num [cell12602])
      exact ⟨E.1,E.2.trans (by norm_num [cell12602])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy44 (n := 12602) (by norm_num)
        (q := 1 - (cell12602 ⟨44,by decide⟩).lower)
        (by norm_num [cell12602]) (by norm_num [cell12602])
      exact ⟨E.1,E.2.trans (by norm_num [cell12602])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy45 (n := 12602) (by norm_num)
        (q := 1 - (cell12602 ⟨45,by decide⟩).lower)
        (by norm_num [cell12602]) (by norm_num [cell12602])
      exact ⟨E.1,E.2.trans (by norm_num [cell12602])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy46 (n := 12602) (by norm_num)
        (q := 1 - (cell12602 ⟨46,by decide⟩).lower)
        (by norm_num [cell12602]) (by norm_num [cell12602])
      exact ⟨E.1,E.2.trans (by norm_num [cell12602])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy47 (n := 12602) (by norm_num)
        (q := 1 - (cell12602 ⟨47,by decide⟩).lower)
        (by norm_num [cell12602]) (by norm_num [cell12602])
      exact ⟨E.1,E.2.trans (by norm_num [cell12602])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy48 (n := 12602) (by norm_num)
        (q := 1 - (cell12602 ⟨48,by decide⟩).lower)
        (by norm_num [cell12602]) (by norm_num [cell12602])
      exact ⟨E.1,E.2.trans (by norm_num [cell12602])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy49 (n := 12602) (by norm_num)
        (q := 1 - (cell12602 ⟨49,by decide⟩).lower)
        (by norm_num [cell12602]) (by norm_num [cell12602])
      exact ⟨E.1,E.2.trans (by norm_num [cell12602])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy50 (n := 12602) (by norm_num)
        (q := 1 - (cell12602 ⟨50,by decide⟩).lower)
        (by norm_num [cell12602]) (by norm_num [cell12602])
      exact ⟨E.1,E.2.trans (by norm_num [cell12602])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy51 (n := 12602) (by norm_num)
        (q := 1 - (cell12602 ⟨51,by decide⟩).lower)
        (by norm_num [cell12602]) (by norm_num [cell12602])
      exact ⟨E.1,E.2.trans (by norm_num [cell12602])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy52 (n := 12602) (by norm_num)
        (q := 1 - (cell12602 ⟨52,by decide⟩).lower)
        (by norm_num [cell12602]) (by norm_num [cell12602])
      exact ⟨E.1,E.2.trans (by norm_num [cell12602])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12602

/-! Source-cell containment and simple scalar guards at 12602. -/
namespace BstLean.Part269.N12602
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12602)
open BstLean.Part268 (cell12602)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12602 ⟨10,by decide⟩).lower ∧ (cell12602 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12602 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12602 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12602 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12602 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12602 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12602,cell12602,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12602 ⟨11,by decide⟩).lower ∧ (cell12602 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12602 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12602 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12602 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12602 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12602 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12602,cell12602,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12602 ⟨12,by decide⟩).lower ∧ (cell12602 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12602 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12602 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12602 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12602 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12602 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12602,cell12602,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12602 ⟨13,by decide⟩).lower ∧ (cell12602 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12602 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12602 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12602 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12602 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12602 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12602,cell12602,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12602 ⟨14,by decide⟩).lower ∧ (cell12602 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12602 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12602 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12602 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12602 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12602 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12602,cell12602,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12602 ⟨15,by decide⟩).lower ∧ (cell12602 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12602 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12602 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12602 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12602 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12602 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12602,cell12602,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12602 ⟨16,by decide⟩).lower ∧ (cell12602 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12602 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12602 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12602 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12602 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12602 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12602,cell12602,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12602 ⟨17,by decide⟩).lower ∧ (cell12602 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12602 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12602 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12602 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12602 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12602 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12602,cell12602,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12602 ⟨18,by decide⟩).lower ∧ (cell12602 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12602 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12602 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12602 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12602 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12602 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12602,cell12602,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12602 ⟨19,by decide⟩).lower ∧ (cell12602 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12602 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12602 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12602 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12602 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12602 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12602,cell12602,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12602 ⟨20,by decide⟩).lower ∧ (cell12602 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12602 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12602 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12602 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12602 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12602 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12602,cell12602,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12602 ⟨21,by decide⟩).lower ∧ (cell12602 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12602 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12602 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12602 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12602 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12602 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12602,cell12602,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12602 ⟨22,by decide⟩).lower ∧ (cell12602 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12602 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12602 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12602 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12602 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12602 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12602,cell12602,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12602 ⟨23,by decide⟩).lower ∧ (cell12602 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12602 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12602 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12602 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12602 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12602 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12602,cell12602,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12602 ⟨24,by decide⟩).lower ∧ (cell12602 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12602 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12602 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12602 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12602 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12602 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12602,cell12602,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12602 ⟨25,by decide⟩).lower ∧ (cell12602 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12602 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12602 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12602 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12602 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12602 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12602,cell12602,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12602 ⟨26,by decide⟩).lower ∧ (cell12602 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12602 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12602 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12602 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12602 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12602 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12602,cell12602,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12602 ⟨27,by decide⟩).lower ∧ (cell12602 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12602 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12602 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12602 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12602 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12602 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12602,cell12602,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12602 ⟨28,by decide⟩).lower ∧ (cell12602 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12602 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12602 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12602 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12602 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12602 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12602,cell12602,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12602 ⟨29,by decide⟩).lower ∧ (cell12602 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12602 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12602 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12602 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12602 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12602 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12602,cell12602,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12602 ⟨30,by decide⟩).lower ∧ (cell12602 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12602 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12602 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12602 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12602 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12602 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12602,cell12602,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12602 ⟨31,by decide⟩).lower ∧ (cell12602 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12602 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12602 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12602 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12602 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12602 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12602,cell12602,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12602 ⟨32,by decide⟩).lower ∧ (cell12602 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12602 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12602 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12602 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12602 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12602 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12602,cell12602,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12602 ⟨33,by decide⟩).lower ∧ (cell12602 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12602 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12602 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12602 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12602 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12602 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12602,cell12602,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12602 ⟨34,by decide⟩).lower ∧ (cell12602 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12602 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12602 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12602 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12602 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12602 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12602,cell12602,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12602 ⟨35,by decide⟩).lower ∧ (cell12602 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12602 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12602 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12602 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12602 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12602 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12602,cell12602,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12602 ⟨36,by decide⟩).lower ∧ (cell12602 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12602 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12602 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12602 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12602 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12602 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12602,cell12602,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12602 ⟨37,by decide⟩).lower ∧ (cell12602 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12602 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12602 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12602 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12602 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12602 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12602,cell12602,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12602 ⟨38,by decide⟩).lower ∧ (cell12602 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12602 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12602 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12602 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12602 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12602 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12602,cell12602,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12602 ⟨39,by decide⟩).lower ∧ (cell12602 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12602 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12602 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12602 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12602 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12602 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12602,cell12602,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12602 ⟨40,by decide⟩).lower ∧ (cell12602 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12602 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12602 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12602 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12602 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12602 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12602,cell12602,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12602 ⟨41,by decide⟩).lower ∧ (cell12602 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12602 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12602 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12602 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12602 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12602 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12602,cell12602,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12602 ⟨42,by decide⟩).lower ∧ (cell12602 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12602 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12602 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12602 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12602 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12602 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12602,cell12602,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12602 ⟨43,by decide⟩).lower ∧ (cell12602 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12602 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12602 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12602 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12602 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12602 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12602,cell12602,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12602 ⟨44,by decide⟩).lower ∧ (cell12602 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12602 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12602 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12602 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12602 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12602 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12602,cell12602,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12602 ⟨45,by decide⟩).lower ∧ (cell12602 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12602 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12602 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12602 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12602 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12602 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12602,cell12602,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12602 ⟨46,by decide⟩).lower ∧ (cell12602 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12602 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12602 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12602 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12602 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12602 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12602,cell12602,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12602 ⟨47,by decide⟩).lower ∧ (cell12602 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12602 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12602 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12602 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12602 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12602 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12602,cell12602,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12602 ⟨48,by decide⟩).lower ∧ (cell12602 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12602 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12602 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12602 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12602 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12602 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12602,cell12602,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12602 ⟨49,by decide⟩).lower ∧ (cell12602 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12602 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12602 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12602 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12602 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12602 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12602,cell12602,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12602 ⟨50,by decide⟩).lower ∧ (cell12602 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12602 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12602 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12602 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12602 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12602 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12602,cell12602,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12602 ⟨51,by decide⟩).lower ∧ (cell12602 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12602 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12602 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12602 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12602 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12602 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12602,cell12602,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12602 ⟨52,by decide⟩).lower ∧ (cell12602 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12602 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12602 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12602 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12602 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12602 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12602,cell12602,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12602 i).lower ∧
    (cell12602 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12602 i).upper ≤ (0.532 : ℝ) ∧
    (cell12602 i).centre ≤ (0.1 : ℝ) ∧ (cell12602 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12602 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12602 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12602

/-! The local source numeric instances at 12602 have no network premises. -/
namespace BstLean.Part269.N12602
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12602)
open BstLean.Part268 (cell12602)

noncomputable def sourceNumerics12602 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12602 (cell12602 i)
      scalarRow12602.M scalarRow12602.H scalarRow12602.xi := by
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
    energy_allowance := scalarRow12602.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12602]
    centre_nonneg := (scalarRow12602.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D10.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12602])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12602
/-! Actual 12603 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12603
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12603 ≤ (1.035947975521 : ℝ) := by
  have hr : (112.263083869988 : ℝ) ≤ √(12603 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.263083869988 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12603 12603 (11 / 1000) ≤
    (0.008514705141 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12603) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.263083869988 : ℝ) ≤ √(12603 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12603)
  have hdiv : K / √(12603 : ℝ) ≤ K / 112.263083869988 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.263083869988 ≤ (0.008514705141 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12603.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12603 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12603 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12603 := gPlus_lower 12603
end BstLean.Part269.N12603

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12603
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035947975520 : ℝ) ≤ wn 12603 := by
  have hn : √(12603 : ℝ) ≤ 112.263083869989 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12603 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.263083869989 ≤ 2 / √(12603 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000253853491 : ℝ) ≤ rhoBar 12603 BstLean.Part154.csC ∧
    rhoBar 12603 BstLean.Part154.csC ≤ 0.000253853884 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035947975520 : ℝ) / (1.295212 * 12603) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035947975521 : ℝ) / (1.29521 * 12603) := by gcongr
      _ ≤ (0.000253853884 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12603 BstLean.Part154.csC) ≤ 0.001015479978 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12603 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12603 BstLean.Part154.csC) (piBar (rhoBar 12603 BstLean.Part154.csC)) ≤ 0.000193895380 ∧
    cc1 (rhoBar 12603 BstLean.Part154.csC) (piBar (rhoBar 12603 BstLean.Part154.csC)) ≤ 0.000123376903 ∧
    cc2 (rhoBar 12603 BstLean.Part154.csC) ≤ 0.000071621220 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12603 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12603 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12603 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12603 BstLean.Part154.csC * nuR (rhoBar 12603 BstLean.Part154.csC)) ≤ 0.000507723879 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000253853884 : ℝ) * 0.001015479978 := by gcongr
      _ ≤ (0.000507723879 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12603 BstLean.Part154.csC) * nuR (rhoBar 12603 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001015479978 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12603 BstLean.Part154.csC) * rhoBar 12603 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000253853884 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000253853884 / 2 + 0.399 * 0.001015479978 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000193895380 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000507723879 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123376903 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000253853884 / 1.414213562 := by gcongr
      _ ≤ (0.000071621220 : ℝ) := by norm_num

end BstLean.Part269.N12603

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12603
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12603 BstLean.Part154.csC) (piBar (rhoBar 12603 BstLean.Part154.csC)) ≤ 1.62357E-7 := by
  have hr0 : 0 ≤ rhoBar 12603 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12603 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12603 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12603 BstLean.Part154.csC) (piBar (rhoBar 12603 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12603 BstLean.Part154.csC) (piBar (rhoBar 12603 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12603 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000193895380 : ℝ) ^ 2 + 0.000123376903 ^ 2 + 3 * 0.000071621220 ^ 2 +
        2 * 0.797885 * 0.000193895380 * 0.000123376903 + 2 * 0.000193895380 * 0.000071621220 +
        4 * 0.797885 * 0.000123376903 * 0.000071621220 := by gcongr
    _ ≤ (1.62357E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12603 BstLean.Part154.csC Θ ≤ 0.002650243727 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12603 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12603 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12603 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12603 BstLean.Part154.csC) (piBar (rhoBar 12603 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12603 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035947975521 * 1.62357E-7 / (0.000253853491 : ℝ) := by gcongr
    _ ≤ 0.002650243727 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12603 BstLean.Part154.csC Θ ≤ 0.002940974560 + 0.000669671727 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12603 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12603 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12603 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035947975521 : ℝ) * ((2 * Θ * 0.000253853884 +
        (6863 / 10000) * 0.000253853884 * 12603 * 0.001015479978) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002940974560 + 0.000669671727 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12603 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12603 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12603 0.011 Θ ∧ gammaRatio 12603 0.011 Θ ≤ 0.000087268401 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12603 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035947975521 : ℝ) * 0.525 / ((1 - 0.011) * 12603) := by gcongr
      _ ≤ (0.000087268401 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12603 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12603 0.011 Θ) :=
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
    badAllowance 12603 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000676285396 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12603 BstLean.Part154.csC) 1.22 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 2 (rhoBar 12603 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12603 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12603 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12603 0.011 Θ) 1.12 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 1 (gammaRatio 12603 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12603 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12603 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12603 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12603 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035947975521 : ℝ) * 12603 *
        (2.5110E-8 / 1.1045361 + 3.0670E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000676285396 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12603 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003617259956 + 0.003319915454 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12603

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12603
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12603 BstLean.Part154.csC) (piBar (rhoBar 12603 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12603 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12603 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12603 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12603 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12603 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12603 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12603 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12603 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12603 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12603 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12603 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12603 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12603 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12603 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052688094824 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12603) ≤ 0.010637847634 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12603 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035947975521)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010637847634 + 2 * 0.737676 / 12603) := by gcongr
    _ ≤ (0.052688094824 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12603 12 ≤ 0.0015 := by
  exact BstLean.Part269.S10.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12603

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12603
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560499147901 : ℝ) ≤ plow 12603 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12603) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052866815570)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001391377957) : eMP 12603 0.011 xi bn ≤ 0.001197708512 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12603 : ℝ) * (1 - 0.011))) ≤ 0.000592191823 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001391377957 / (12603 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000592191823 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000592191823 : ℝ) + 3.141593 * 0.052866815570 / (12603 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001197708512 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052866815570)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001391377957) : PiBarMP 12603 12 0.011 xi bn ≤ 0.161876651805 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12603 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037301179030 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.643929525971 : ℝ) ≤ √((12603 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.263083869988 : ℝ) ≤ √(12603 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12603) ≤ 0.124104984315 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037301179030 + 0.052866815570 * 1.772454 / (2 * (111.643929525971 : ℝ))) * (1 + 0.001197708512) +
        8 / (12603 * 112.263083869988) + 0.124104984315 := by gcongr
    _ ≤ (0.161876651805 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052866815570)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001391377957) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282615943442) :
    parallelOracle 12603 0.011 xi bn cd ≤ 0.162874855720 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12603 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12603 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560499147901 : ℝ) ≤ plow 12603 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.263083869988 : ℝ) ≤ √(12603 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282615943442 : ℝ) / (2 * 0.560499147901 * 112.263083869988)) * 0.161876651805 +
        0.282615943442 ^ 2 / (2 * 0.560499147901 * 112.263083869988) := by gcongr
    _ ≤ (0.162874855720 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052866815570) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001391377957)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282615943442) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12603 12603 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560499147901 : ℝ) ≤ plow 12603 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.263083869988 : ℝ) ≤ √(12603 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12603 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12603 Θ 1.22 ≤ 0.011812436059 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.263083869988 := by gcongr <;> linarith
      _ ≤ (0.011812436059 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12603 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12603 12603 0.011 ≤ 0.008514705141 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12603 12603 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12603 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12603 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12603 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12603 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162874855720 + 0.011812436059 + (0.008514705141 : ℝ) *
        (1 + 2 * (0.282615943442 + 0.011812436059) / (0.560499147901 * 112.263083869988))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12603]

end BstLean.Part269.N12603

/-! The original eight local profiles supply actual 12603 moment certificates. -/
namespace BstLean.Part269.N12603
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12603 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12603 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12603 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052866815570 ∧
    0 ≤ bN 12603 BstLean.Part154.csC (groupTheta g) ∧ bN 12603 BstLean.Part154.csC (groupTheta g) ≤ 0.001391377957 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12603 12603 0.011
      (momentAllowance 12603 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12603 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12603 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12603 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12603 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12603 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229927848618 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12603 0.011
      (momentAllowance 12603 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12603 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12603
/-! The actual computed-centre upper energy formula at 12603. -/
namespace BstLean.Part269.N12603
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12603

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12603
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12603)
open BstLean.Part268 (cell12603)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085778408567
  | 2 => 0.086726573330
  | 3 => 0.087673687185
  | 4 => 0.088621353235
  | 5 => 0.089571504161
  | 6 => 0.090526450343
  | 7 => 0.091488932354
  | 8 => 0.092462177840
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12603 12603 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12603 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12603

/-! Actual upper energy certificates on all 43 source endpoints at 12603. -/
namespace BstLean.Part269.N12603
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12603)
open BstLean.Part268 (cell12603)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12603 (gMinus 12603) (1 - (cell12603 i).lower) ≤ 1 ∧
    energyUpper 12603 (gMinus 12603) (BstLean.Part211.gPlus 12603)
      (finiteEnergy 12603 12603 0.011) (1 - (cell12603 i).lower) ≤
      (cell12603 i).energy := by
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
      have E := BstLean.Part269.S10.uniformEnergy10 (n := 12603) (by norm_num)
        (q := 1 - (cell12603 ⟨10,by decide⟩).lower)
        (by norm_num [cell12603]) (by norm_num [cell12603])
      exact ⟨E.1,E.2.trans (by norm_num [cell12603])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy11 (n := 12603) (by norm_num)
        (q := 1 - (cell12603 ⟨11,by decide⟩).lower)
        (by norm_num [cell12603]) (by norm_num [cell12603])
      exact ⟨E.1,E.2.trans (by norm_num [cell12603])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy12 (n := 12603) (by norm_num)
        (q := 1 - (cell12603 ⟨12,by decide⟩).lower)
        (by norm_num [cell12603]) (by norm_num [cell12603])
      exact ⟨E.1,E.2.trans (by norm_num [cell12603])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy13 (n := 12603) (by norm_num)
        (q := 1 - (cell12603 ⟨13,by decide⟩).lower)
        (by norm_num [cell12603]) (by norm_num [cell12603])
      exact ⟨E.1,E.2.trans (by norm_num [cell12603])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy14 (n := 12603) (by norm_num)
        (q := 1 - (cell12603 ⟨14,by decide⟩).lower)
        (by norm_num [cell12603]) (by norm_num [cell12603])
      exact ⟨E.1,E.2.trans (by norm_num [cell12603])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy15 (n := 12603) (by norm_num)
        (q := 1 - (cell12603 ⟨15,by decide⟩).lower)
        (by norm_num [cell12603]) (by norm_num [cell12603])
      exact ⟨E.1,E.2.trans (by norm_num [cell12603])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy16 (n := 12603) (by norm_num)
        (q := 1 - (cell12603 ⟨16,by decide⟩).lower)
        (by norm_num [cell12603]) (by norm_num [cell12603])
      exact ⟨E.1,E.2.trans (by norm_num [cell12603])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy17 (n := 12603) (by norm_num)
        (q := 1 - (cell12603 ⟨17,by decide⟩).lower)
        (by norm_num [cell12603]) (by norm_num [cell12603])
      exact ⟨E.1,E.2.trans (by norm_num [cell12603])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy18 (n := 12603) (by norm_num)
        (q := 1 - (cell12603 ⟨18,by decide⟩).lower)
        (by norm_num [cell12603]) (by norm_num [cell12603])
      exact ⟨E.1,E.2.trans (by norm_num [cell12603])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy19 (n := 12603) (by norm_num)
        (q := 1 - (cell12603 ⟨19,by decide⟩).lower)
        (by norm_num [cell12603]) (by norm_num [cell12603])
      exact ⟨E.1,E.2.trans (by norm_num [cell12603])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy20 (n := 12603) (by norm_num)
        (q := 1 - (cell12603 ⟨20,by decide⟩).lower)
        (by norm_num [cell12603]) (by norm_num [cell12603])
      exact ⟨E.1,E.2.trans (by norm_num [cell12603])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy21 (n := 12603) (by norm_num)
        (q := 1 - (cell12603 ⟨21,by decide⟩).lower)
        (by norm_num [cell12603]) (by norm_num [cell12603])
      exact ⟨E.1,E.2.trans (by norm_num [cell12603])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy22 (n := 12603) (by norm_num)
        (q := 1 - (cell12603 ⟨22,by decide⟩).lower)
        (by norm_num [cell12603]) (by norm_num [cell12603])
      exact ⟨E.1,E.2.trans (by norm_num [cell12603])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy23 (n := 12603) (by norm_num)
        (q := 1 - (cell12603 ⟨23,by decide⟩).lower)
        (by norm_num [cell12603]) (by norm_num [cell12603])
      exact ⟨E.1,E.2.trans (by norm_num [cell12603])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy24 (n := 12603) (by norm_num)
        (q := 1 - (cell12603 ⟨24,by decide⟩).lower)
        (by norm_num [cell12603]) (by norm_num [cell12603])
      exact ⟨E.1,E.2.trans (by norm_num [cell12603])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy25 (n := 12603) (by norm_num)
        (q := 1 - (cell12603 ⟨25,by decide⟩).lower)
        (by norm_num [cell12603]) (by norm_num [cell12603])
      exact ⟨E.1,E.2.trans (by norm_num [cell12603])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy26 (n := 12603) (by norm_num)
        (q := 1 - (cell12603 ⟨26,by decide⟩).lower)
        (by norm_num [cell12603]) (by norm_num [cell12603])
      exact ⟨E.1,E.2.trans (by norm_num [cell12603])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy27 (n := 12603) (by norm_num)
        (q := 1 - (cell12603 ⟨27,by decide⟩).lower)
        (by norm_num [cell12603]) (by norm_num [cell12603])
      exact ⟨E.1,E.2.trans (by norm_num [cell12603])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy28 (n := 12603) (by norm_num)
        (q := 1 - (cell12603 ⟨28,by decide⟩).lower)
        (by norm_num [cell12603]) (by norm_num [cell12603])
      exact ⟨E.1,E.2.trans (by norm_num [cell12603])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy29 (n := 12603) (by norm_num)
        (q := 1 - (cell12603 ⟨29,by decide⟩).lower)
        (by norm_num [cell12603]) (by norm_num [cell12603])
      exact ⟨E.1,E.2.trans (by norm_num [cell12603])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy30 (n := 12603) (by norm_num)
        (q := 1 - (cell12603 ⟨30,by decide⟩).lower)
        (by norm_num [cell12603]) (by norm_num [cell12603])
      exact ⟨E.1,E.2.trans (by norm_num [cell12603])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy31 (n := 12603) (by norm_num)
        (q := 1 - (cell12603 ⟨31,by decide⟩).lower)
        (by norm_num [cell12603]) (by norm_num [cell12603])
      exact ⟨E.1,E.2.trans (by norm_num [cell12603])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy32 (n := 12603) (by norm_num)
        (q := 1 - (cell12603 ⟨32,by decide⟩).lower)
        (by norm_num [cell12603]) (by norm_num [cell12603])
      exact ⟨E.1,E.2.trans (by norm_num [cell12603])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy33 (n := 12603) (by norm_num)
        (q := 1 - (cell12603 ⟨33,by decide⟩).lower)
        (by norm_num [cell12603]) (by norm_num [cell12603])
      exact ⟨E.1,E.2.trans (by norm_num [cell12603])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy34 (n := 12603) (by norm_num)
        (q := 1 - (cell12603 ⟨34,by decide⟩).lower)
        (by norm_num [cell12603]) (by norm_num [cell12603])
      exact ⟨E.1,E.2.trans (by norm_num [cell12603])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy35 (n := 12603) (by norm_num)
        (q := 1 - (cell12603 ⟨35,by decide⟩).lower)
        (by norm_num [cell12603]) (by norm_num [cell12603])
      exact ⟨E.1,E.2.trans (by norm_num [cell12603])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy36 (n := 12603) (by norm_num)
        (q := 1 - (cell12603 ⟨36,by decide⟩).lower)
        (by norm_num [cell12603]) (by norm_num [cell12603])
      exact ⟨E.1,E.2.trans (by norm_num [cell12603])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy37 (n := 12603) (by norm_num)
        (q := 1 - (cell12603 ⟨37,by decide⟩).lower)
        (by norm_num [cell12603]) (by norm_num [cell12603])
      exact ⟨E.1,E.2.trans (by norm_num [cell12603])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy38 (n := 12603) (by norm_num)
        (q := 1 - (cell12603 ⟨38,by decide⟩).lower)
        (by norm_num [cell12603]) (by norm_num [cell12603])
      exact ⟨E.1,E.2.trans (by norm_num [cell12603])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy39 (n := 12603) (by norm_num)
        (q := 1 - (cell12603 ⟨39,by decide⟩).lower)
        (by norm_num [cell12603]) (by norm_num [cell12603])
      exact ⟨E.1,E.2.trans (by norm_num [cell12603])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy40 (n := 12603) (by norm_num)
        (q := 1 - (cell12603 ⟨40,by decide⟩).lower)
        (by norm_num [cell12603]) (by norm_num [cell12603])
      exact ⟨E.1,E.2.trans (by norm_num [cell12603])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy41 (n := 12603) (by norm_num)
        (q := 1 - (cell12603 ⟨41,by decide⟩).lower)
        (by norm_num [cell12603]) (by norm_num [cell12603])
      exact ⟨E.1,E.2.trans (by norm_num [cell12603])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy42 (n := 12603) (by norm_num)
        (q := 1 - (cell12603 ⟨42,by decide⟩).lower)
        (by norm_num [cell12603]) (by norm_num [cell12603])
      exact ⟨E.1,E.2.trans (by norm_num [cell12603])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy43 (n := 12603) (by norm_num)
        (q := 1 - (cell12603 ⟨43,by decide⟩).lower)
        (by norm_num [cell12603]) (by norm_num [cell12603])
      exact ⟨E.1,E.2.trans (by norm_num [cell12603])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy44 (n := 12603) (by norm_num)
        (q := 1 - (cell12603 ⟨44,by decide⟩).lower)
        (by norm_num [cell12603]) (by norm_num [cell12603])
      exact ⟨E.1,E.2.trans (by norm_num [cell12603])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy45 (n := 12603) (by norm_num)
        (q := 1 - (cell12603 ⟨45,by decide⟩).lower)
        (by norm_num [cell12603]) (by norm_num [cell12603])
      exact ⟨E.1,E.2.trans (by norm_num [cell12603])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy46 (n := 12603) (by norm_num)
        (q := 1 - (cell12603 ⟨46,by decide⟩).lower)
        (by norm_num [cell12603]) (by norm_num [cell12603])
      exact ⟨E.1,E.2.trans (by norm_num [cell12603])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy47 (n := 12603) (by norm_num)
        (q := 1 - (cell12603 ⟨47,by decide⟩).lower)
        (by norm_num [cell12603]) (by norm_num [cell12603])
      exact ⟨E.1,E.2.trans (by norm_num [cell12603])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy48 (n := 12603) (by norm_num)
        (q := 1 - (cell12603 ⟨48,by decide⟩).lower)
        (by norm_num [cell12603]) (by norm_num [cell12603])
      exact ⟨E.1,E.2.trans (by norm_num [cell12603])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy49 (n := 12603) (by norm_num)
        (q := 1 - (cell12603 ⟨49,by decide⟩).lower)
        (by norm_num [cell12603]) (by norm_num [cell12603])
      exact ⟨E.1,E.2.trans (by norm_num [cell12603])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy50 (n := 12603) (by norm_num)
        (q := 1 - (cell12603 ⟨50,by decide⟩).lower)
        (by norm_num [cell12603]) (by norm_num [cell12603])
      exact ⟨E.1,E.2.trans (by norm_num [cell12603])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy51 (n := 12603) (by norm_num)
        (q := 1 - (cell12603 ⟨51,by decide⟩).lower)
        (by norm_num [cell12603]) (by norm_num [cell12603])
      exact ⟨E.1,E.2.trans (by norm_num [cell12603])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy52 (n := 12603) (by norm_num)
        (q := 1 - (cell12603 ⟨52,by decide⟩).lower)
        (by norm_num [cell12603]) (by norm_num [cell12603])
      exact ⟨E.1,E.2.trans (by norm_num [cell12603])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12603

/-! Source-cell containment and simple scalar guards at 12603. -/
namespace BstLean.Part269.N12603
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12603)
open BstLean.Part268 (cell12603)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12603 ⟨10,by decide⟩).lower ∧ (cell12603 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12603 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12603 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12603 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12603 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12603 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12603,cell12603,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12603 ⟨11,by decide⟩).lower ∧ (cell12603 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12603 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12603 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12603 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12603 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12603 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12603,cell12603,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12603 ⟨12,by decide⟩).lower ∧ (cell12603 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12603 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12603 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12603 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12603 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12603 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12603,cell12603,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12603 ⟨13,by decide⟩).lower ∧ (cell12603 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12603 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12603 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12603 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12603 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12603 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12603,cell12603,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12603 ⟨14,by decide⟩).lower ∧ (cell12603 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12603 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12603 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12603 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12603 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12603 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12603,cell12603,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12603 ⟨15,by decide⟩).lower ∧ (cell12603 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12603 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12603 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12603 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12603 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12603 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12603,cell12603,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12603 ⟨16,by decide⟩).lower ∧ (cell12603 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12603 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12603 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12603 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12603 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12603 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12603,cell12603,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12603 ⟨17,by decide⟩).lower ∧ (cell12603 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12603 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12603 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12603 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12603 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12603 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12603,cell12603,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12603 ⟨18,by decide⟩).lower ∧ (cell12603 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12603 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12603 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12603 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12603 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12603 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12603,cell12603,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12603 ⟨19,by decide⟩).lower ∧ (cell12603 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12603 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12603 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12603 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12603 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12603 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12603,cell12603,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12603 ⟨20,by decide⟩).lower ∧ (cell12603 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12603 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12603 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12603 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12603 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12603 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12603,cell12603,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12603 ⟨21,by decide⟩).lower ∧ (cell12603 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12603 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12603 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12603 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12603 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12603 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12603,cell12603,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12603 ⟨22,by decide⟩).lower ∧ (cell12603 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12603 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12603 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12603 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12603 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12603 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12603,cell12603,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12603 ⟨23,by decide⟩).lower ∧ (cell12603 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12603 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12603 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12603 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12603 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12603 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12603,cell12603,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12603 ⟨24,by decide⟩).lower ∧ (cell12603 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12603 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12603 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12603 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12603 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12603 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12603,cell12603,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12603 ⟨25,by decide⟩).lower ∧ (cell12603 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12603 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12603 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12603 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12603 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12603 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12603,cell12603,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12603 ⟨26,by decide⟩).lower ∧ (cell12603 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12603 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12603 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12603 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12603 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12603 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12603,cell12603,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12603 ⟨27,by decide⟩).lower ∧ (cell12603 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12603 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12603 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12603 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12603 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12603 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12603,cell12603,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12603 ⟨28,by decide⟩).lower ∧ (cell12603 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12603 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12603 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12603 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12603 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12603 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12603,cell12603,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12603 ⟨29,by decide⟩).lower ∧ (cell12603 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12603 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12603 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12603 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12603 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12603 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12603,cell12603,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12603 ⟨30,by decide⟩).lower ∧ (cell12603 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12603 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12603 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12603 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12603 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12603 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12603,cell12603,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12603 ⟨31,by decide⟩).lower ∧ (cell12603 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12603 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12603 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12603 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12603 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12603 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12603,cell12603,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12603 ⟨32,by decide⟩).lower ∧ (cell12603 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12603 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12603 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12603 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12603 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12603 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12603,cell12603,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12603 ⟨33,by decide⟩).lower ∧ (cell12603 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12603 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12603 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12603 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12603 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12603 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12603,cell12603,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12603 ⟨34,by decide⟩).lower ∧ (cell12603 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12603 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12603 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12603 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12603 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12603 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12603,cell12603,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12603 ⟨35,by decide⟩).lower ∧ (cell12603 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12603 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12603 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12603 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12603 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12603 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12603,cell12603,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12603 ⟨36,by decide⟩).lower ∧ (cell12603 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12603 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12603 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12603 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12603 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12603 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12603,cell12603,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12603 ⟨37,by decide⟩).lower ∧ (cell12603 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12603 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12603 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12603 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12603 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12603 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12603,cell12603,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12603 ⟨38,by decide⟩).lower ∧ (cell12603 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12603 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12603 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12603 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12603 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12603 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12603,cell12603,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12603 ⟨39,by decide⟩).lower ∧ (cell12603 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12603 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12603 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12603 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12603 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12603 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12603,cell12603,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12603 ⟨40,by decide⟩).lower ∧ (cell12603 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12603 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12603 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12603 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12603 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12603 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12603,cell12603,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12603 ⟨41,by decide⟩).lower ∧ (cell12603 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12603 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12603 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12603 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12603 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12603 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12603,cell12603,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12603 ⟨42,by decide⟩).lower ∧ (cell12603 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12603 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12603 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12603 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12603 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12603 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12603,cell12603,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12603 ⟨43,by decide⟩).lower ∧ (cell12603 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12603 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12603 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12603 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12603 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12603 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12603,cell12603,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12603 ⟨44,by decide⟩).lower ∧ (cell12603 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12603 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12603 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12603 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12603 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12603 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12603,cell12603,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12603 ⟨45,by decide⟩).lower ∧ (cell12603 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12603 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12603 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12603 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12603 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12603 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12603,cell12603,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12603 ⟨46,by decide⟩).lower ∧ (cell12603 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12603 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12603 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12603 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12603 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12603 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12603,cell12603,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12603 ⟨47,by decide⟩).lower ∧ (cell12603 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12603 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12603 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12603 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12603 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12603 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12603,cell12603,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12603 ⟨48,by decide⟩).lower ∧ (cell12603 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12603 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12603 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12603 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12603 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12603 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12603,cell12603,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12603 ⟨49,by decide⟩).lower ∧ (cell12603 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12603 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12603 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12603 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12603 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12603 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12603,cell12603,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12603 ⟨50,by decide⟩).lower ∧ (cell12603 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12603 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12603 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12603 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12603 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12603 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12603,cell12603,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12603 ⟨51,by decide⟩).lower ∧ (cell12603 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12603 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12603 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12603 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12603 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12603 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12603,cell12603,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12603 ⟨52,by decide⟩).lower ∧ (cell12603 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12603 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12603 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12603 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12603 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12603 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12603,cell12603,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12603 i).lower ∧
    (cell12603 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12603 i).upper ≤ (0.532 : ℝ) ∧
    (cell12603 i).centre ≤ (0.1 : ℝ) ∧ (cell12603 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12603 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12603 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12603

/-! The local source numeric instances at 12603 have no network premises. -/
namespace BstLean.Part269.N12603
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12603)
open BstLean.Part268 (cell12603)

noncomputable def sourceNumerics12603 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12603 (cell12603 i)
      scalarRow12603.M scalarRow12603.H scalarRow12603.xi := by
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
    energy_allowance := scalarRow12603.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12603]
    centre_nonneg := (scalarRow12603.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D10.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12603])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12603
/-! Actual 12604 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12604
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12604 ≤ (1.035946536848 : ℝ) := by
  have hr : (112.267537605489 : ℝ) ≤ √(12604 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.267537605489 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12604 12604 (11 / 1000) ≤
    (0.008514367354 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12604) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.267537605489 : ℝ) ≤ √(12604 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12604)
  have hdiv : K / √(12604 : ℝ) ≤ K / 112.267537605489 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.267537605489 ≤ (0.008514367354 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12604.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12604 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12604 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12604 := gPlus_lower 12604
end BstLean.Part269.N12604

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12604
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035946536847 : ℝ) ≤ wn 12604 := by
  have hn : √(12604 : ℝ) ≤ 112.267537605490 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12604 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.267537605490 ≤ 2 / √(12604 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000253832998 : ℝ) ≤ rhoBar 12604 BstLean.Part154.csC ∧
    rhoBar 12604 BstLean.Part154.csC ≤ 0.000253833391 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035946536847 : ℝ) / (1.295212 * 12604) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035946536848 : ℝ) / (1.29521 * 12604) := by gcongr
      _ ≤ (0.000253833391 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12604 BstLean.Part154.csC) ≤ 0.001015397996 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12604 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12604 BstLean.Part154.csC) (piBar (rhoBar 12604 BstLean.Part154.csC)) ≤ 0.000193879726 ∧
    cc1 (rhoBar 12604 BstLean.Part154.csC) (piBar (rhoBar 12604 BstLean.Part154.csC)) ≤ 0.000123366943 ∧
    cc2 (rhoBar 12604 BstLean.Part154.csC) ≤ 0.000071615438 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12604 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12604 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12604 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12604 BstLean.Part154.csC * nuR (rhoBar 12604 BstLean.Part154.csC)) ≤ 0.000507682890 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000253833391 : ℝ) * 0.001015397996 := by gcongr
      _ ≤ (0.000507682890 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12604 BstLean.Part154.csC) * nuR (rhoBar 12604 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001015397996 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12604 BstLean.Part154.csC) * rhoBar 12604 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000253833391 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000253833391 / 2 + 0.399 * 0.001015397996 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000193879726 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000507682890 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123366943 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000253833391 / 1.414213562 := by gcongr
      _ ≤ (0.000071615438 : ℝ) := by norm_num

end BstLean.Part269.N12604

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12604
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12604 BstLean.Part154.csC) (piBar (rhoBar 12604 BstLean.Part154.csC)) ≤ 1.62330E-7 := by
  have hr0 : 0 ≤ rhoBar 12604 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12604 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12604 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12604 BstLean.Part154.csC) (piBar (rhoBar 12604 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12604 BstLean.Part154.csC) (piBar (rhoBar 12604 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12604 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000193879726 : ℝ) ^ 2 + 0.000123366943 ^ 2 + 3 * 0.000071615438 ^ 2 +
        2 * 0.797885 * 0.000193879726 * 0.000123366943 + 2 * 0.000193879726 * 0.000071615438 +
        4 * 0.797885 * 0.000123366943 * 0.000071615438 := by gcongr
    _ ≤ (1.62330E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12604 BstLean.Part154.csC Θ ≤ 0.002650013240 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12604 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12604 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12604 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12604 BstLean.Part154.csC) (piBar (rhoBar 12604 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12604 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035946536848 * 1.62330E-7 / (0.000253832998 : ℝ) := by gcongr
    _ ≤ 0.002650013240 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12604 BstLean.Part154.csC Θ ≤ 0.002940728963 + 0.000669616736 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12604 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12604 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12604 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035946536848 : ℝ) * ((2 * Θ * 0.000253833391 +
        (6863 / 10000) * 0.000253833391 * 12604 * 0.001015397996) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002940728963 + 0.000669616736 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12604 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12604 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12604 0.011 Θ ∧ gammaRatio 12604 0.011 Θ ≤ 0.000087261356 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12604 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035946536848 : ℝ) * 0.525 / ((1 - 0.011) * 12604) := by gcongr
      _ ≤ (0.000087261356 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12604 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12604 0.011 Θ) :=
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
    badAllowance 12604 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000676285396 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12604 BstLean.Part154.csC) 1.22 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 2 (rhoBar 12604 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12604 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12604 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12604 0.011 Θ) 1.12 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 1 (gammaRatio 12604 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12604 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12604 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12604 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12604 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035946536848 : ℝ) * 12604 *
        (2.5110E-8 / 1.1045361 + 3.0670E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000676285396 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12604 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003617014359 + 0.003319629976 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12604

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12604
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12604 BstLean.Part154.csC) (piBar (rhoBar 12604 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12604 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12604 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12604 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12604 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12604 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12604 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12604 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12604 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12604 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12604 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12604 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12604 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12604 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12604 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052685981899 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12604) ≤ 0.010637425623 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12604 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035946536848)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010637425623 + 2 * 0.737676 / 12604) := by gcongr
    _ ≤ (0.052685981899 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12604 12 ≤ 0.0015 := by
  exact BstLean.Part269.S10.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12604

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12604
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560499193819 : ℝ) ≤ plow 12604 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12604) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052866420097)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001391256951) : eMP 12604 0.011 xi bn ≤ 0.001197608867 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12604 : ℝ) * (1 - 0.011))) ≤ 0.000592142579 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001391256951 / (12604 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000592142579 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000592142579 : ℝ) + 3.141593 * 0.052866420097 / (12604 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001197608867 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052866420097)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001391256951) : PiBarMP 12604 12 0.011 xi bn ≤ 0.161870080236 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12604 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037299556982 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.648358698191 : ℝ) ≤ √((12604 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.267537605489 : ℝ) ≤ √(12604 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12604) ≤ 0.124100060979 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037299556982 + 0.052866420097 * 1.772454 / (2 * (111.648358698191 : ℝ))) * (1 + 0.001197608867) +
        8 / (12604 * 112.267537605489) + 0.124100060979 := by gcongr
    _ ≤ (0.161870080236 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052866420097)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001391256951) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282612970522) :
    parallelOracle 12604 0.011 xi bn cd ≤ 0.162868212536 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12604 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12604 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560499193819 : ℝ) ≤ plow 12604 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.267537605489 : ℝ) ≤ √(12604 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282612970522 : ℝ) / (2 * 0.560499193819 * 112.267537605489)) * 0.161870080236 +
        0.282612970522 ^ 2 / (2 * 0.560499193819 * 112.267537605489) := by gcongr
    _ ≤ (0.162868212536 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052866420097) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001391256951)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282612970522) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12604 12604 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560499193819 : ℝ) ≤ plow 12604 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.267537605489 : ℝ) ≤ √(12604 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12604 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12604 Θ 1.22 ≤ 0.011811967452 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.267537605489 := by gcongr <;> linarith
      _ ≤ (0.011811967452 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12604 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12604 12604 0.011 ≤ 0.008514367354 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12604 12604 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12604 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12604 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12604 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12604 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162868212536 + 0.011811967452 + (0.008514367354 : ℝ) *
        (1 + 2 * (0.282612970522 + 0.011811967452) / (0.560499193819 * 112.267537605489))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12604]

end BstLean.Part269.N12604

/-! The original eight local profiles supply actual 12604 moment certificates. -/
namespace BstLean.Part269.N12604
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12604 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12604 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12604 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052866420097 ∧
    0 ≤ bN 12604 BstLean.Part154.csC (groupTheta g) ∧ bN 12604 BstLean.Part154.csC (groupTheta g) ≤ 0.001391256951 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12604 12604 0.011
      (momentAllowance 12604 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12604 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12604 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12604 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12604 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12604 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229926988623 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12604 0.011
      (momentAllowance 12604 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12604 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12604
/-! The actual computed-centre upper energy formula at 12604. -/
namespace BstLean.Part269.N12604
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12604

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12604
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12604)
open BstLean.Part268 (cell12604)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085775382341
  | 2 => 0.086723488951
  | 3 => 0.087670535763
  | 4 => 0.088618123862
  | 5 => 0.089568183562
  | 6 => 0.090523022479
  | 7 => 0.091485377986
  | 8 => 0.092458474047
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12604 12604 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12604 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12604

/-! Actual upper energy certificates on all 43 source endpoints at 12604. -/
namespace BstLean.Part269.N12604
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12604)
open BstLean.Part268 (cell12604)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12604 (gMinus 12604) (1 - (cell12604 i).lower) ≤ 1 ∧
    energyUpper 12604 (gMinus 12604) (BstLean.Part211.gPlus 12604)
      (finiteEnergy 12604 12604 0.011) (1 - (cell12604 i).lower) ≤
      (cell12604 i).energy := by
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
      have E := BstLean.Part269.S10.uniformEnergy10 (n := 12604) (by norm_num)
        (q := 1 - (cell12604 ⟨10,by decide⟩).lower)
        (by norm_num [cell12604]) (by norm_num [cell12604])
      exact ⟨E.1,E.2.trans (by norm_num [cell12604])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy11 (n := 12604) (by norm_num)
        (q := 1 - (cell12604 ⟨11,by decide⟩).lower)
        (by norm_num [cell12604]) (by norm_num [cell12604])
      exact ⟨E.1,E.2.trans (by norm_num [cell12604])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy12 (n := 12604) (by norm_num)
        (q := 1 - (cell12604 ⟨12,by decide⟩).lower)
        (by norm_num [cell12604]) (by norm_num [cell12604])
      exact ⟨E.1,E.2.trans (by norm_num [cell12604])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy13 (n := 12604) (by norm_num)
        (q := 1 - (cell12604 ⟨13,by decide⟩).lower)
        (by norm_num [cell12604]) (by norm_num [cell12604])
      exact ⟨E.1,E.2.trans (by norm_num [cell12604])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy14 (n := 12604) (by norm_num)
        (q := 1 - (cell12604 ⟨14,by decide⟩).lower)
        (by norm_num [cell12604]) (by norm_num [cell12604])
      exact ⟨E.1,E.2.trans (by norm_num [cell12604])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy15 (n := 12604) (by norm_num)
        (q := 1 - (cell12604 ⟨15,by decide⟩).lower)
        (by norm_num [cell12604]) (by norm_num [cell12604])
      exact ⟨E.1,E.2.trans (by norm_num [cell12604])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy16 (n := 12604) (by norm_num)
        (q := 1 - (cell12604 ⟨16,by decide⟩).lower)
        (by norm_num [cell12604]) (by norm_num [cell12604])
      exact ⟨E.1,E.2.trans (by norm_num [cell12604])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy17 (n := 12604) (by norm_num)
        (q := 1 - (cell12604 ⟨17,by decide⟩).lower)
        (by norm_num [cell12604]) (by norm_num [cell12604])
      exact ⟨E.1,E.2.trans (by norm_num [cell12604])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy18 (n := 12604) (by norm_num)
        (q := 1 - (cell12604 ⟨18,by decide⟩).lower)
        (by norm_num [cell12604]) (by norm_num [cell12604])
      exact ⟨E.1,E.2.trans (by norm_num [cell12604])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy19 (n := 12604) (by norm_num)
        (q := 1 - (cell12604 ⟨19,by decide⟩).lower)
        (by norm_num [cell12604]) (by norm_num [cell12604])
      exact ⟨E.1,E.2.trans (by norm_num [cell12604])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy20 (n := 12604) (by norm_num)
        (q := 1 - (cell12604 ⟨20,by decide⟩).lower)
        (by norm_num [cell12604]) (by norm_num [cell12604])
      exact ⟨E.1,E.2.trans (by norm_num [cell12604])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy21 (n := 12604) (by norm_num)
        (q := 1 - (cell12604 ⟨21,by decide⟩).lower)
        (by norm_num [cell12604]) (by norm_num [cell12604])
      exact ⟨E.1,E.2.trans (by norm_num [cell12604])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy22 (n := 12604) (by norm_num)
        (q := 1 - (cell12604 ⟨22,by decide⟩).lower)
        (by norm_num [cell12604]) (by norm_num [cell12604])
      exact ⟨E.1,E.2.trans (by norm_num [cell12604])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy23 (n := 12604) (by norm_num)
        (q := 1 - (cell12604 ⟨23,by decide⟩).lower)
        (by norm_num [cell12604]) (by norm_num [cell12604])
      exact ⟨E.1,E.2.trans (by norm_num [cell12604])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy24 (n := 12604) (by norm_num)
        (q := 1 - (cell12604 ⟨24,by decide⟩).lower)
        (by norm_num [cell12604]) (by norm_num [cell12604])
      exact ⟨E.1,E.2.trans (by norm_num [cell12604])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy25 (n := 12604) (by norm_num)
        (q := 1 - (cell12604 ⟨25,by decide⟩).lower)
        (by norm_num [cell12604]) (by norm_num [cell12604])
      exact ⟨E.1,E.2.trans (by norm_num [cell12604])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy26 (n := 12604) (by norm_num)
        (q := 1 - (cell12604 ⟨26,by decide⟩).lower)
        (by norm_num [cell12604]) (by norm_num [cell12604])
      exact ⟨E.1,E.2.trans (by norm_num [cell12604])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy27 (n := 12604) (by norm_num)
        (q := 1 - (cell12604 ⟨27,by decide⟩).lower)
        (by norm_num [cell12604]) (by norm_num [cell12604])
      exact ⟨E.1,E.2.trans (by norm_num [cell12604])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy28 (n := 12604) (by norm_num)
        (q := 1 - (cell12604 ⟨28,by decide⟩).lower)
        (by norm_num [cell12604]) (by norm_num [cell12604])
      exact ⟨E.1,E.2.trans (by norm_num [cell12604])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy29 (n := 12604) (by norm_num)
        (q := 1 - (cell12604 ⟨29,by decide⟩).lower)
        (by norm_num [cell12604]) (by norm_num [cell12604])
      exact ⟨E.1,E.2.trans (by norm_num [cell12604])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy30 (n := 12604) (by norm_num)
        (q := 1 - (cell12604 ⟨30,by decide⟩).lower)
        (by norm_num [cell12604]) (by norm_num [cell12604])
      exact ⟨E.1,E.2.trans (by norm_num [cell12604])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy31 (n := 12604) (by norm_num)
        (q := 1 - (cell12604 ⟨31,by decide⟩).lower)
        (by norm_num [cell12604]) (by norm_num [cell12604])
      exact ⟨E.1,E.2.trans (by norm_num [cell12604])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy32 (n := 12604) (by norm_num)
        (q := 1 - (cell12604 ⟨32,by decide⟩).lower)
        (by norm_num [cell12604]) (by norm_num [cell12604])
      exact ⟨E.1,E.2.trans (by norm_num [cell12604])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy33 (n := 12604) (by norm_num)
        (q := 1 - (cell12604 ⟨33,by decide⟩).lower)
        (by norm_num [cell12604]) (by norm_num [cell12604])
      exact ⟨E.1,E.2.trans (by norm_num [cell12604])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy34 (n := 12604) (by norm_num)
        (q := 1 - (cell12604 ⟨34,by decide⟩).lower)
        (by norm_num [cell12604]) (by norm_num [cell12604])
      exact ⟨E.1,E.2.trans (by norm_num [cell12604])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy35 (n := 12604) (by norm_num)
        (q := 1 - (cell12604 ⟨35,by decide⟩).lower)
        (by norm_num [cell12604]) (by norm_num [cell12604])
      exact ⟨E.1,E.2.trans (by norm_num [cell12604])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy36 (n := 12604) (by norm_num)
        (q := 1 - (cell12604 ⟨36,by decide⟩).lower)
        (by norm_num [cell12604]) (by norm_num [cell12604])
      exact ⟨E.1,E.2.trans (by norm_num [cell12604])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy37 (n := 12604) (by norm_num)
        (q := 1 - (cell12604 ⟨37,by decide⟩).lower)
        (by norm_num [cell12604]) (by norm_num [cell12604])
      exact ⟨E.1,E.2.trans (by norm_num [cell12604])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy38 (n := 12604) (by norm_num)
        (q := 1 - (cell12604 ⟨38,by decide⟩).lower)
        (by norm_num [cell12604]) (by norm_num [cell12604])
      exact ⟨E.1,E.2.trans (by norm_num [cell12604])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy39 (n := 12604) (by norm_num)
        (q := 1 - (cell12604 ⟨39,by decide⟩).lower)
        (by norm_num [cell12604]) (by norm_num [cell12604])
      exact ⟨E.1,E.2.trans (by norm_num [cell12604])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy40 (n := 12604) (by norm_num)
        (q := 1 - (cell12604 ⟨40,by decide⟩).lower)
        (by norm_num [cell12604]) (by norm_num [cell12604])
      exact ⟨E.1,E.2.trans (by norm_num [cell12604])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy41 (n := 12604) (by norm_num)
        (q := 1 - (cell12604 ⟨41,by decide⟩).lower)
        (by norm_num [cell12604]) (by norm_num [cell12604])
      exact ⟨E.1,E.2.trans (by norm_num [cell12604])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy42 (n := 12604) (by norm_num)
        (q := 1 - (cell12604 ⟨42,by decide⟩).lower)
        (by norm_num [cell12604]) (by norm_num [cell12604])
      exact ⟨E.1,E.2.trans (by norm_num [cell12604])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy43 (n := 12604) (by norm_num)
        (q := 1 - (cell12604 ⟨43,by decide⟩).lower)
        (by norm_num [cell12604]) (by norm_num [cell12604])
      exact ⟨E.1,E.2.trans (by norm_num [cell12604])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy44 (n := 12604) (by norm_num)
        (q := 1 - (cell12604 ⟨44,by decide⟩).lower)
        (by norm_num [cell12604]) (by norm_num [cell12604])
      exact ⟨E.1,E.2.trans (by norm_num [cell12604])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy45 (n := 12604) (by norm_num)
        (q := 1 - (cell12604 ⟨45,by decide⟩).lower)
        (by norm_num [cell12604]) (by norm_num [cell12604])
      exact ⟨E.1,E.2.trans (by norm_num [cell12604])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy46 (n := 12604) (by norm_num)
        (q := 1 - (cell12604 ⟨46,by decide⟩).lower)
        (by norm_num [cell12604]) (by norm_num [cell12604])
      exact ⟨E.1,E.2.trans (by norm_num [cell12604])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy47 (n := 12604) (by norm_num)
        (q := 1 - (cell12604 ⟨47,by decide⟩).lower)
        (by norm_num [cell12604]) (by norm_num [cell12604])
      exact ⟨E.1,E.2.trans (by norm_num [cell12604])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy48 (n := 12604) (by norm_num)
        (q := 1 - (cell12604 ⟨48,by decide⟩).lower)
        (by norm_num [cell12604]) (by norm_num [cell12604])
      exact ⟨E.1,E.2.trans (by norm_num [cell12604])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy49 (n := 12604) (by norm_num)
        (q := 1 - (cell12604 ⟨49,by decide⟩).lower)
        (by norm_num [cell12604]) (by norm_num [cell12604])
      exact ⟨E.1,E.2.trans (by norm_num [cell12604])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy50 (n := 12604) (by norm_num)
        (q := 1 - (cell12604 ⟨50,by decide⟩).lower)
        (by norm_num [cell12604]) (by norm_num [cell12604])
      exact ⟨E.1,E.2.trans (by norm_num [cell12604])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy51 (n := 12604) (by norm_num)
        (q := 1 - (cell12604 ⟨51,by decide⟩).lower)
        (by norm_num [cell12604]) (by norm_num [cell12604])
      exact ⟨E.1,E.2.trans (by norm_num [cell12604])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy52 (n := 12604) (by norm_num)
        (q := 1 - (cell12604 ⟨52,by decide⟩).lower)
        (by norm_num [cell12604]) (by norm_num [cell12604])
      exact ⟨E.1,E.2.trans (by norm_num [cell12604])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12604

/-! Source-cell containment and simple scalar guards at 12604. -/
namespace BstLean.Part269.N12604
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12604)
open BstLean.Part268 (cell12604)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12604 ⟨10,by decide⟩).lower ∧ (cell12604 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12604 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12604 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12604 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12604 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12604 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12604,cell12604,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12604 ⟨11,by decide⟩).lower ∧ (cell12604 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12604 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12604 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12604 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12604 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12604 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12604,cell12604,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12604 ⟨12,by decide⟩).lower ∧ (cell12604 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12604 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12604 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12604 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12604 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12604 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12604,cell12604,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12604 ⟨13,by decide⟩).lower ∧ (cell12604 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12604 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12604 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12604 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12604 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12604 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12604,cell12604,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12604 ⟨14,by decide⟩).lower ∧ (cell12604 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12604 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12604 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12604 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12604 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12604 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12604,cell12604,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12604 ⟨15,by decide⟩).lower ∧ (cell12604 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12604 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12604 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12604 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12604 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12604 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12604,cell12604,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12604 ⟨16,by decide⟩).lower ∧ (cell12604 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12604 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12604 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12604 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12604 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12604 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12604,cell12604,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12604 ⟨17,by decide⟩).lower ∧ (cell12604 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12604 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12604 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12604 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12604 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12604 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12604,cell12604,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12604 ⟨18,by decide⟩).lower ∧ (cell12604 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12604 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12604 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12604 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12604 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12604 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12604,cell12604,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12604 ⟨19,by decide⟩).lower ∧ (cell12604 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12604 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12604 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12604 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12604 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12604 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12604,cell12604,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12604 ⟨20,by decide⟩).lower ∧ (cell12604 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12604 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12604 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12604 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12604 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12604 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12604,cell12604,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12604 ⟨21,by decide⟩).lower ∧ (cell12604 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12604 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12604 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12604 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12604 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12604 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12604,cell12604,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12604 ⟨22,by decide⟩).lower ∧ (cell12604 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12604 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12604 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12604 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12604 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12604 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12604,cell12604,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12604 ⟨23,by decide⟩).lower ∧ (cell12604 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12604 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12604 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12604 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12604 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12604 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12604,cell12604,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12604 ⟨24,by decide⟩).lower ∧ (cell12604 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12604 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12604 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12604 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12604 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12604 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12604,cell12604,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12604 ⟨25,by decide⟩).lower ∧ (cell12604 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12604 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12604 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12604 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12604 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12604 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12604,cell12604,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12604 ⟨26,by decide⟩).lower ∧ (cell12604 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12604 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12604 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12604 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12604 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12604 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12604,cell12604,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12604 ⟨27,by decide⟩).lower ∧ (cell12604 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12604 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12604 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12604 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12604 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12604 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12604,cell12604,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12604 ⟨28,by decide⟩).lower ∧ (cell12604 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12604 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12604 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12604 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12604 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12604 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12604,cell12604,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12604 ⟨29,by decide⟩).lower ∧ (cell12604 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12604 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12604 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12604 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12604 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12604 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12604,cell12604,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12604 ⟨30,by decide⟩).lower ∧ (cell12604 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12604 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12604 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12604 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12604 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12604 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12604,cell12604,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12604 ⟨31,by decide⟩).lower ∧ (cell12604 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12604 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12604 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12604 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12604 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12604 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12604,cell12604,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12604 ⟨32,by decide⟩).lower ∧ (cell12604 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12604 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12604 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12604 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12604 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12604 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12604,cell12604,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12604 ⟨33,by decide⟩).lower ∧ (cell12604 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12604 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12604 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12604 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12604 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12604 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12604,cell12604,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12604 ⟨34,by decide⟩).lower ∧ (cell12604 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12604 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12604 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12604 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12604 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12604 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12604,cell12604,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12604 ⟨35,by decide⟩).lower ∧ (cell12604 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12604 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12604 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12604 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12604 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12604 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12604,cell12604,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12604 ⟨36,by decide⟩).lower ∧ (cell12604 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12604 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12604 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12604 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12604 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12604 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12604,cell12604,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12604 ⟨37,by decide⟩).lower ∧ (cell12604 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12604 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12604 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12604 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12604 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12604 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12604,cell12604,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12604 ⟨38,by decide⟩).lower ∧ (cell12604 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12604 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12604 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12604 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12604 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12604 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12604,cell12604,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12604 ⟨39,by decide⟩).lower ∧ (cell12604 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12604 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12604 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12604 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12604 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12604 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12604,cell12604,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12604 ⟨40,by decide⟩).lower ∧ (cell12604 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12604 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12604 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12604 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12604 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12604 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12604,cell12604,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12604 ⟨41,by decide⟩).lower ∧ (cell12604 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12604 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12604 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12604 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12604 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12604 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12604,cell12604,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12604 ⟨42,by decide⟩).lower ∧ (cell12604 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12604 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12604 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12604 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12604 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12604 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12604,cell12604,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12604 ⟨43,by decide⟩).lower ∧ (cell12604 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12604 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12604 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12604 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12604 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12604 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12604,cell12604,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12604 ⟨44,by decide⟩).lower ∧ (cell12604 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12604 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12604 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12604 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12604 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12604 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12604,cell12604,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12604 ⟨45,by decide⟩).lower ∧ (cell12604 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12604 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12604 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12604 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12604 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12604 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12604,cell12604,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12604 ⟨46,by decide⟩).lower ∧ (cell12604 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12604 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12604 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12604 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12604 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12604 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12604,cell12604,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12604 ⟨47,by decide⟩).lower ∧ (cell12604 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12604 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12604 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12604 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12604 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12604 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12604,cell12604,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12604 ⟨48,by decide⟩).lower ∧ (cell12604 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12604 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12604 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12604 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12604 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12604 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12604,cell12604,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12604 ⟨49,by decide⟩).lower ∧ (cell12604 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12604 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12604 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12604 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12604 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12604 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12604,cell12604,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12604 ⟨50,by decide⟩).lower ∧ (cell12604 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12604 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12604 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12604 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12604 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12604 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12604,cell12604,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12604 ⟨51,by decide⟩).lower ∧ (cell12604 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12604 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12604 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12604 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12604 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12604 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12604,cell12604,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12604 ⟨52,by decide⟩).lower ∧ (cell12604 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12604 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12604 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12604 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12604 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12604 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12604,cell12604,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12604 i).lower ∧
    (cell12604 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12604 i).upper ≤ (0.532 : ℝ) ∧
    (cell12604 i).centre ≤ (0.1 : ℝ) ∧ (cell12604 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12604 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12604 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12604

/-! The local source numeric instances at 12604 have no network premises. -/
namespace BstLean.Part269.N12604
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12604)
open BstLean.Part268 (cell12604)

noncomputable def sourceNumerics12604 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12604 (cell12604 i)
      scalarRow12604.M scalarRow12604.H scalarRow12604.xi := by
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
    energy_allowance := scalarRow12604.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12604]
    centre_nonneg := (scalarRow12604.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D10.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12604])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12604
/-! Actual 12605 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12605
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12605 ≤ (1.035945098347 : ℝ) := by
  have hr : (112.271991164314 : ℝ) ≤ √(12605 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.271991164314 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12605 12605 (11 / 1000) ≤
    (0.008514029607 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12605) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.271991164314 : ℝ) ≤ √(12605 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12605)
  have hdiv : K / √(12605 : ℝ) ≤ K / 112.271991164314 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.271991164314 ≤ (0.008514029607 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12605.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12605 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12605 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12605 := gPlus_lower 12605
end BstLean.Part269.N12605

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12605
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035945098346 : ℝ) ≤ wn 12605 := by
  have hn : √(12605 : ℝ) ≤ 112.271991164315 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12605 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.271991164315 ≤ 2 / √(12605 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000253812508 : ℝ) ≤ rhoBar 12605 BstLean.Part154.csC ∧
    rhoBar 12605 BstLean.Part154.csC ≤ 0.000253812901 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035945098346 : ℝ) / (1.295212 * 12605) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035945098347 : ℝ) / (1.29521 * 12605) := by gcongr
      _ ≤ (0.000253812901 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12605 BstLean.Part154.csC) ≤ 0.001015316025 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12605 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12605 BstLean.Part154.csC) (piBar (rhoBar 12605 BstLean.Part154.csC)) ≤ 0.000193864075 ∧
    cc1 (rhoBar 12605 BstLean.Part154.csC) (piBar (rhoBar 12605 BstLean.Part154.csC)) ≤ 0.000123356984 ∧
    cc2 (rhoBar 12605 BstLean.Part154.csC) ≤ 0.000071609657 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12605 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12605 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12605 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12605 BstLean.Part154.csC * nuR (rhoBar 12605 BstLean.Part154.csC)) ≤ 0.000507641907 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000253812901 : ℝ) * 0.001015316025 := by gcongr
      _ ≤ (0.000507641907 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12605 BstLean.Part154.csC) * nuR (rhoBar 12605 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001015316025 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12605 BstLean.Part154.csC) * rhoBar 12605 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000253812901 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000253812901 / 2 + 0.399 * 0.001015316025 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000193864075 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000507641907 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123356984 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000253812901 / 1.414213562 := by gcongr
      _ ≤ (0.000071609657 : ℝ) := by norm_num

end BstLean.Part269.N12605

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12605
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12605 BstLean.Part154.csC) (piBar (rhoBar 12605 BstLean.Part154.csC)) ≤ 1.62304E-7 := by
  have hr0 : 0 ≤ rhoBar 12605 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12605 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12605 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12605 BstLean.Part154.csC) (piBar (rhoBar 12605 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12605 BstLean.Part154.csC) (piBar (rhoBar 12605 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12605 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000193864075 : ℝ) ^ 2 + 0.000123356984 ^ 2 + 3 * 0.000071609657 ^ 2 +
        2 * 0.797885 * 0.000193864075 * 0.000123356984 + 2 * 0.000193864075 * 0.000071609657 +
        4 * 0.797885 * 0.000123356984 * 0.000071609657 := by gcongr
    _ ≤ (1.62304E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12605 BstLean.Part154.csC Θ ≤ 0.002649799013 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12605 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12605 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12605 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12605 BstLean.Part154.csC) (piBar (rhoBar 12605 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12605 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035945098347 * 1.62304E-7 / (0.000253812508 : ℝ) := by gcongr
    _ ≤ 0.002649799013 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12605 BstLean.Part154.csC Θ ≤ 0.002940483397 + 0.000669561753 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12605 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12605 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12605 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035945098347 : ℝ) * ((2 * Θ * 0.000253812901 +
        (6863 / 10000) * 0.000253812901 * 12605 * 0.001015316025) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002940483397 + 0.000669561753 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12605 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12605 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12605 0.011 Θ ∧ gammaRatio 12605 0.011 Θ ≤ 0.000087254312 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12605 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035945098347 : ℝ) * 0.525 / ((1 - 0.011) * 12605) := by gcongr
      _ ≤ (0.000087254312 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12605 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12605 0.011 Θ) :=
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
    badAllowance 12605 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000676285396 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12605 BstLean.Part154.csC) 1.22 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 2 (rhoBar 12605 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12605 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12605 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12605 0.011 Θ) 1.12 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 1 (gammaRatio 12605 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12605 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12605 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12605 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12605 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035945098347 : ℝ) * 12605 *
        (2.5110E-8 / 1.1045361 + 3.0670E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000676285396 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12605 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003616768793 + 0.003319360766 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12605

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12605
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12605 BstLean.Part154.csC) (piBar (rhoBar 12605 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12605 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12605 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12605 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12605 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12605 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12605 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12605 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12605 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12605 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12605 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12605 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12605 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12605 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12605 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052683869227 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12605) ≤ 0.010637003662 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12605 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035945098347)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010637003662 + 2 * 0.737676 / 12605) := by gcongr
    _ ≤ (0.052683869227 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12605 12 ≤ 0.0015 := by
  exact BstLean.Part269.S10.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12605

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12605
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560499239730 : ℝ) ≤ plow 12605 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12605) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052866033196)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001391144482) : eMP 12605 0.011 xi bn ≤ 0.001197512869 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12605 : ℝ) * (1 - 0.011))) ≤ 0.000592095157 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001391144482 / (12605 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000592095157 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000592095157 : ℝ) + 3.141593 * 0.052866033196 / (12605 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001197512869 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052866033196)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001391144482) : PiBarMP 12605 12 0.011 xi bn ≤ 0.161863623971 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12605 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037298049306 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.652787694710 : ℝ) ≤ √((12605 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.271991164314 : ℝ) ≤ √(12605 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12605) ≤ 0.124095138229 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037298049306 + 0.052866033196 * 1.772454 / (2 * (111.652787694710 : ℝ))) * (1 + 0.001197512869) +
        8 / (12605 * 112.271991164314) + 0.124095138229 := by gcongr
    _ ≤ (0.161863623971 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052866033196)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001391144482) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282610016492) :
    parallelOracle 12605 0.011 xi bn cd ≤ 0.162861685033 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12605 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12605 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560499239730 : ℝ) ≤ plow 12605 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.271991164314 : ℝ) ≤ √(12605 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282610016492 : ℝ) / (2 * 0.560499239730 * 112.271991164314)) * 0.161863623971 +
        0.282610016492 ^ 2 / (2 * 0.560499239730 * 112.271991164314) := by gcongr
    _ ≤ (0.162861685033 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052866033196) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001391144482)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282610016492) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12605 12605 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560499239730 : ℝ) ≤ plow 12605 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.271991164314 : ℝ) ≤ √(12605 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12605 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12605 Θ 1.22 ≤ 0.011811498899 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.271991164314 := by gcongr <;> linarith
      _ ≤ (0.011811498899 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12605 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12605 12605 0.011 ≤ 0.008514029607 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12605 12605 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12605 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12605 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12605 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12605 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162861685033 + 0.011811498899 + (0.008514029607 : ℝ) *
        (1 + 2 * (0.282610016492 + 0.011811498899) / (0.560499239730 * 112.271991164314))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12605]

end BstLean.Part269.N12605

/-! The original eight local profiles supply actual 12605 moment certificates. -/
namespace BstLean.Part269.N12605
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12605 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12605 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12605 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052866033196 ∧
    0 ≤ bN 12605 BstLean.Part154.csC (groupTheta g) ∧ bN 12605 BstLean.Part154.csC (groupTheta g) ≤ 0.001391144482 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12605 12605 0.011
      (momentAllowance 12605 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12605 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12605 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12605 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12605 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12605 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229926147265 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12605 0.011
      (momentAllowance 12605 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12605 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12605
/-! The actual computed-centre upper energy formula at 12605. -/
namespace BstLean.Part269.N12605
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12605

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12605
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12605)
open BstLean.Part268 (cell12605)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085772357311
  | 2 => 0.086720405818
  | 3 => 0.087667385649
  | 4 => 0.088614895875
  | 5 => 0.089564864441
  | 6 => 0.090519596207
  | 7 => 0.091481825348
  | 8 => 0.092454772146
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12605 12605 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12605 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12605

/-! Actual upper energy certificates on all 43 source endpoints at 12605. -/
namespace BstLean.Part269.N12605
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12605)
open BstLean.Part268 (cell12605)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12605 (gMinus 12605) (1 - (cell12605 i).lower) ≤ 1 ∧
    energyUpper 12605 (gMinus 12605) (BstLean.Part211.gPlus 12605)
      (finiteEnergy 12605 12605 0.011) (1 - (cell12605 i).lower) ≤
      (cell12605 i).energy := by
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
      have E := BstLean.Part269.S10.uniformEnergy10 (n := 12605) (by norm_num)
        (q := 1 - (cell12605 ⟨10,by decide⟩).lower)
        (by norm_num [cell12605]) (by norm_num [cell12605])
      exact ⟨E.1,E.2.trans (by norm_num [cell12605])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy11 (n := 12605) (by norm_num)
        (q := 1 - (cell12605 ⟨11,by decide⟩).lower)
        (by norm_num [cell12605]) (by norm_num [cell12605])
      exact ⟨E.1,E.2.trans (by norm_num [cell12605])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy12 (n := 12605) (by norm_num)
        (q := 1 - (cell12605 ⟨12,by decide⟩).lower)
        (by norm_num [cell12605]) (by norm_num [cell12605])
      exact ⟨E.1,E.2.trans (by norm_num [cell12605])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy13 (n := 12605) (by norm_num)
        (q := 1 - (cell12605 ⟨13,by decide⟩).lower)
        (by norm_num [cell12605]) (by norm_num [cell12605])
      exact ⟨E.1,E.2.trans (by norm_num [cell12605])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy14 (n := 12605) (by norm_num)
        (q := 1 - (cell12605 ⟨14,by decide⟩).lower)
        (by norm_num [cell12605]) (by norm_num [cell12605])
      exact ⟨E.1,E.2.trans (by norm_num [cell12605])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy15 (n := 12605) (by norm_num)
        (q := 1 - (cell12605 ⟨15,by decide⟩).lower)
        (by norm_num [cell12605]) (by norm_num [cell12605])
      exact ⟨E.1,E.2.trans (by norm_num [cell12605])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy16 (n := 12605) (by norm_num)
        (q := 1 - (cell12605 ⟨16,by decide⟩).lower)
        (by norm_num [cell12605]) (by norm_num [cell12605])
      exact ⟨E.1,E.2.trans (by norm_num [cell12605])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy17 (n := 12605) (by norm_num)
        (q := 1 - (cell12605 ⟨17,by decide⟩).lower)
        (by norm_num [cell12605]) (by norm_num [cell12605])
      exact ⟨E.1,E.2.trans (by norm_num [cell12605])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy18 (n := 12605) (by norm_num)
        (q := 1 - (cell12605 ⟨18,by decide⟩).lower)
        (by norm_num [cell12605]) (by norm_num [cell12605])
      exact ⟨E.1,E.2.trans (by norm_num [cell12605])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy19 (n := 12605) (by norm_num)
        (q := 1 - (cell12605 ⟨19,by decide⟩).lower)
        (by norm_num [cell12605]) (by norm_num [cell12605])
      exact ⟨E.1,E.2.trans (by norm_num [cell12605])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy20 (n := 12605) (by norm_num)
        (q := 1 - (cell12605 ⟨20,by decide⟩).lower)
        (by norm_num [cell12605]) (by norm_num [cell12605])
      exact ⟨E.1,E.2.trans (by norm_num [cell12605])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy21 (n := 12605) (by norm_num)
        (q := 1 - (cell12605 ⟨21,by decide⟩).lower)
        (by norm_num [cell12605]) (by norm_num [cell12605])
      exact ⟨E.1,E.2.trans (by norm_num [cell12605])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy22 (n := 12605) (by norm_num)
        (q := 1 - (cell12605 ⟨22,by decide⟩).lower)
        (by norm_num [cell12605]) (by norm_num [cell12605])
      exact ⟨E.1,E.2.trans (by norm_num [cell12605])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy23 (n := 12605) (by norm_num)
        (q := 1 - (cell12605 ⟨23,by decide⟩).lower)
        (by norm_num [cell12605]) (by norm_num [cell12605])
      exact ⟨E.1,E.2.trans (by norm_num [cell12605])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy24 (n := 12605) (by norm_num)
        (q := 1 - (cell12605 ⟨24,by decide⟩).lower)
        (by norm_num [cell12605]) (by norm_num [cell12605])
      exact ⟨E.1,E.2.trans (by norm_num [cell12605])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy25 (n := 12605) (by norm_num)
        (q := 1 - (cell12605 ⟨25,by decide⟩).lower)
        (by norm_num [cell12605]) (by norm_num [cell12605])
      exact ⟨E.1,E.2.trans (by norm_num [cell12605])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy26 (n := 12605) (by norm_num)
        (q := 1 - (cell12605 ⟨26,by decide⟩).lower)
        (by norm_num [cell12605]) (by norm_num [cell12605])
      exact ⟨E.1,E.2.trans (by norm_num [cell12605])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy27 (n := 12605) (by norm_num)
        (q := 1 - (cell12605 ⟨27,by decide⟩).lower)
        (by norm_num [cell12605]) (by norm_num [cell12605])
      exact ⟨E.1,E.2.trans (by norm_num [cell12605])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy28 (n := 12605) (by norm_num)
        (q := 1 - (cell12605 ⟨28,by decide⟩).lower)
        (by norm_num [cell12605]) (by norm_num [cell12605])
      exact ⟨E.1,E.2.trans (by norm_num [cell12605])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy29 (n := 12605) (by norm_num)
        (q := 1 - (cell12605 ⟨29,by decide⟩).lower)
        (by norm_num [cell12605]) (by norm_num [cell12605])
      exact ⟨E.1,E.2.trans (by norm_num [cell12605])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy30 (n := 12605) (by norm_num)
        (q := 1 - (cell12605 ⟨30,by decide⟩).lower)
        (by norm_num [cell12605]) (by norm_num [cell12605])
      exact ⟨E.1,E.2.trans (by norm_num [cell12605])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy31 (n := 12605) (by norm_num)
        (q := 1 - (cell12605 ⟨31,by decide⟩).lower)
        (by norm_num [cell12605]) (by norm_num [cell12605])
      exact ⟨E.1,E.2.trans (by norm_num [cell12605])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy32 (n := 12605) (by norm_num)
        (q := 1 - (cell12605 ⟨32,by decide⟩).lower)
        (by norm_num [cell12605]) (by norm_num [cell12605])
      exact ⟨E.1,E.2.trans (by norm_num [cell12605])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy33 (n := 12605) (by norm_num)
        (q := 1 - (cell12605 ⟨33,by decide⟩).lower)
        (by norm_num [cell12605]) (by norm_num [cell12605])
      exact ⟨E.1,E.2.trans (by norm_num [cell12605])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy34 (n := 12605) (by norm_num)
        (q := 1 - (cell12605 ⟨34,by decide⟩).lower)
        (by norm_num [cell12605]) (by norm_num [cell12605])
      exact ⟨E.1,E.2.trans (by norm_num [cell12605])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy35 (n := 12605) (by norm_num)
        (q := 1 - (cell12605 ⟨35,by decide⟩).lower)
        (by norm_num [cell12605]) (by norm_num [cell12605])
      exact ⟨E.1,E.2.trans (by norm_num [cell12605])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy36 (n := 12605) (by norm_num)
        (q := 1 - (cell12605 ⟨36,by decide⟩).lower)
        (by norm_num [cell12605]) (by norm_num [cell12605])
      exact ⟨E.1,E.2.trans (by norm_num [cell12605])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy37 (n := 12605) (by norm_num)
        (q := 1 - (cell12605 ⟨37,by decide⟩).lower)
        (by norm_num [cell12605]) (by norm_num [cell12605])
      exact ⟨E.1,E.2.trans (by norm_num [cell12605])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy38 (n := 12605) (by norm_num)
        (q := 1 - (cell12605 ⟨38,by decide⟩).lower)
        (by norm_num [cell12605]) (by norm_num [cell12605])
      exact ⟨E.1,E.2.trans (by norm_num [cell12605])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy39 (n := 12605) (by norm_num)
        (q := 1 - (cell12605 ⟨39,by decide⟩).lower)
        (by norm_num [cell12605]) (by norm_num [cell12605])
      exact ⟨E.1,E.2.trans (by norm_num [cell12605])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy40 (n := 12605) (by norm_num)
        (q := 1 - (cell12605 ⟨40,by decide⟩).lower)
        (by norm_num [cell12605]) (by norm_num [cell12605])
      exact ⟨E.1,E.2.trans (by norm_num [cell12605])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy41 (n := 12605) (by norm_num)
        (q := 1 - (cell12605 ⟨41,by decide⟩).lower)
        (by norm_num [cell12605]) (by norm_num [cell12605])
      exact ⟨E.1,E.2.trans (by norm_num [cell12605])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy42 (n := 12605) (by norm_num)
        (q := 1 - (cell12605 ⟨42,by decide⟩).lower)
        (by norm_num [cell12605]) (by norm_num [cell12605])
      exact ⟨E.1,E.2.trans (by norm_num [cell12605])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy43 (n := 12605) (by norm_num)
        (q := 1 - (cell12605 ⟨43,by decide⟩).lower)
        (by norm_num [cell12605]) (by norm_num [cell12605])
      exact ⟨E.1,E.2.trans (by norm_num [cell12605])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy44 (n := 12605) (by norm_num)
        (q := 1 - (cell12605 ⟨44,by decide⟩).lower)
        (by norm_num [cell12605]) (by norm_num [cell12605])
      exact ⟨E.1,E.2.trans (by norm_num [cell12605])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy45 (n := 12605) (by norm_num)
        (q := 1 - (cell12605 ⟨45,by decide⟩).lower)
        (by norm_num [cell12605]) (by norm_num [cell12605])
      exact ⟨E.1,E.2.trans (by norm_num [cell12605])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy46 (n := 12605) (by norm_num)
        (q := 1 - (cell12605 ⟨46,by decide⟩).lower)
        (by norm_num [cell12605]) (by norm_num [cell12605])
      exact ⟨E.1,E.2.trans (by norm_num [cell12605])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy47 (n := 12605) (by norm_num)
        (q := 1 - (cell12605 ⟨47,by decide⟩).lower)
        (by norm_num [cell12605]) (by norm_num [cell12605])
      exact ⟨E.1,E.2.trans (by norm_num [cell12605])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy48 (n := 12605) (by norm_num)
        (q := 1 - (cell12605 ⟨48,by decide⟩).lower)
        (by norm_num [cell12605]) (by norm_num [cell12605])
      exact ⟨E.1,E.2.trans (by norm_num [cell12605])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy49 (n := 12605) (by norm_num)
        (q := 1 - (cell12605 ⟨49,by decide⟩).lower)
        (by norm_num [cell12605]) (by norm_num [cell12605])
      exact ⟨E.1,E.2.trans (by norm_num [cell12605])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy50 (n := 12605) (by norm_num)
        (q := 1 - (cell12605 ⟨50,by decide⟩).lower)
        (by norm_num [cell12605]) (by norm_num [cell12605])
      exact ⟨E.1,E.2.trans (by norm_num [cell12605])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy51 (n := 12605) (by norm_num)
        (q := 1 - (cell12605 ⟨51,by decide⟩).lower)
        (by norm_num [cell12605]) (by norm_num [cell12605])
      exact ⟨E.1,E.2.trans (by norm_num [cell12605])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy52 (n := 12605) (by norm_num)
        (q := 1 - (cell12605 ⟨52,by decide⟩).lower)
        (by norm_num [cell12605]) (by norm_num [cell12605])
      exact ⟨E.1,E.2.trans (by norm_num [cell12605])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12605

/-! Source-cell containment and simple scalar guards at 12605. -/
namespace BstLean.Part269.N12605
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12605)
open BstLean.Part268 (cell12605)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12605 ⟨10,by decide⟩).lower ∧ (cell12605 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12605 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12605 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12605 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12605 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12605 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12605,cell12605,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12605 ⟨11,by decide⟩).lower ∧ (cell12605 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12605 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12605 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12605 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12605 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12605 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12605,cell12605,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12605 ⟨12,by decide⟩).lower ∧ (cell12605 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12605 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12605 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12605 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12605 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12605 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12605,cell12605,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12605 ⟨13,by decide⟩).lower ∧ (cell12605 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12605 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12605 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12605 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12605 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12605 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12605,cell12605,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12605 ⟨14,by decide⟩).lower ∧ (cell12605 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12605 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12605 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12605 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12605 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12605 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12605,cell12605,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12605 ⟨15,by decide⟩).lower ∧ (cell12605 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12605 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12605 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12605 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12605 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12605 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12605,cell12605,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12605 ⟨16,by decide⟩).lower ∧ (cell12605 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12605 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12605 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12605 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12605 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12605 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12605,cell12605,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12605 ⟨17,by decide⟩).lower ∧ (cell12605 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12605 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12605 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12605 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12605 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12605 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12605,cell12605,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12605 ⟨18,by decide⟩).lower ∧ (cell12605 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12605 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12605 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12605 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12605 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12605 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12605,cell12605,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12605 ⟨19,by decide⟩).lower ∧ (cell12605 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12605 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12605 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12605 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12605 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12605 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12605,cell12605,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12605 ⟨20,by decide⟩).lower ∧ (cell12605 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12605 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12605 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12605 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12605 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12605 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12605,cell12605,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12605 ⟨21,by decide⟩).lower ∧ (cell12605 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12605 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12605 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12605 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12605 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12605 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12605,cell12605,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12605 ⟨22,by decide⟩).lower ∧ (cell12605 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12605 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12605 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12605 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12605 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12605 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12605,cell12605,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12605 ⟨23,by decide⟩).lower ∧ (cell12605 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12605 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12605 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12605 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12605 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12605 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12605,cell12605,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12605 ⟨24,by decide⟩).lower ∧ (cell12605 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12605 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12605 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12605 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12605 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12605 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12605,cell12605,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12605 ⟨25,by decide⟩).lower ∧ (cell12605 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12605 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12605 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12605 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12605 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12605 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12605,cell12605,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12605 ⟨26,by decide⟩).lower ∧ (cell12605 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12605 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12605 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12605 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12605 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12605 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12605,cell12605,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12605 ⟨27,by decide⟩).lower ∧ (cell12605 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12605 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12605 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12605 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12605 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12605 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12605,cell12605,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12605 ⟨28,by decide⟩).lower ∧ (cell12605 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12605 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12605 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12605 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12605 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12605 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12605,cell12605,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12605 ⟨29,by decide⟩).lower ∧ (cell12605 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12605 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12605 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12605 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12605 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12605 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12605,cell12605,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12605 ⟨30,by decide⟩).lower ∧ (cell12605 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12605 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12605 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12605 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12605 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12605 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12605,cell12605,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12605 ⟨31,by decide⟩).lower ∧ (cell12605 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12605 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12605 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12605 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12605 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12605 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12605,cell12605,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12605 ⟨32,by decide⟩).lower ∧ (cell12605 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12605 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12605 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12605 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12605 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12605 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12605,cell12605,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12605 ⟨33,by decide⟩).lower ∧ (cell12605 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12605 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12605 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12605 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12605 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12605 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12605,cell12605,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12605 ⟨34,by decide⟩).lower ∧ (cell12605 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12605 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12605 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12605 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12605 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12605 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12605,cell12605,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12605 ⟨35,by decide⟩).lower ∧ (cell12605 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12605 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12605 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12605 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12605 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12605 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12605,cell12605,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12605 ⟨36,by decide⟩).lower ∧ (cell12605 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12605 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12605 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12605 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12605 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12605 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12605,cell12605,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12605 ⟨37,by decide⟩).lower ∧ (cell12605 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12605 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12605 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12605 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12605 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12605 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12605,cell12605,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12605 ⟨38,by decide⟩).lower ∧ (cell12605 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12605 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12605 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12605 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12605 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12605 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12605,cell12605,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12605 ⟨39,by decide⟩).lower ∧ (cell12605 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12605 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12605 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12605 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12605 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12605 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12605,cell12605,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12605 ⟨40,by decide⟩).lower ∧ (cell12605 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12605 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12605 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12605 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12605 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12605 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12605,cell12605,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12605 ⟨41,by decide⟩).lower ∧ (cell12605 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12605 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12605 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12605 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12605 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12605 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12605,cell12605,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12605 ⟨42,by decide⟩).lower ∧ (cell12605 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12605 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12605 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12605 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12605 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12605 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12605,cell12605,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12605 ⟨43,by decide⟩).lower ∧ (cell12605 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12605 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12605 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12605 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12605 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12605 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12605,cell12605,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12605 ⟨44,by decide⟩).lower ∧ (cell12605 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12605 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12605 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12605 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12605 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12605 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12605,cell12605,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12605 ⟨45,by decide⟩).lower ∧ (cell12605 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12605 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12605 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12605 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12605 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12605 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12605,cell12605,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12605 ⟨46,by decide⟩).lower ∧ (cell12605 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12605 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12605 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12605 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12605 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12605 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12605,cell12605,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12605 ⟨47,by decide⟩).lower ∧ (cell12605 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12605 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12605 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12605 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12605 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12605 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12605,cell12605,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12605 ⟨48,by decide⟩).lower ∧ (cell12605 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12605 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12605 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12605 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12605 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12605 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12605,cell12605,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12605 ⟨49,by decide⟩).lower ∧ (cell12605 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12605 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12605 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12605 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12605 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12605 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12605,cell12605,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12605 ⟨50,by decide⟩).lower ∧ (cell12605 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12605 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12605 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12605 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12605 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12605 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12605,cell12605,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12605 ⟨51,by decide⟩).lower ∧ (cell12605 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12605 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12605 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12605 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12605 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12605 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12605,cell12605,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12605 ⟨52,by decide⟩).lower ∧ (cell12605 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12605 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12605 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12605 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12605 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12605 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12605,cell12605,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12605 i).lower ∧
    (cell12605 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12605 i).upper ≤ (0.532 : ℝ) ∧
    (cell12605 i).centre ≤ (0.1 : ℝ) ∧ (cell12605 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12605 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12605 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12605

/-! The local source numeric instances at 12605 have no network premises. -/
namespace BstLean.Part269.N12605
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12605)
open BstLean.Part268 (cell12605)

noncomputable def sourceNumerics12605 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12605 (cell12605 i)
      scalarRow12605.M scalarRow12605.H scalarRow12605.xi := by
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
    energy_allowance := scalarRow12605.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12605]
    centre_nonneg := (scalarRow12605.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D10.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12605])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12605
/-! Actual 12606 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12606
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12606 ≤ (1.035943660018 : ℝ) := by
  have hr : (112.276444546485 : ℝ) ≤ √(12606 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.276444546485 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12606 12606 (11 / 1000) ≤
    (0.008513691900 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12606) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.276444546485 : ℝ) ≤ √(12606 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12606)
  have hdiv : K / √(12606 : ℝ) ≤ K / 112.276444546485 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.276444546485 ≤ (0.008513691900 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12606.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12606 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12606 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12606 := gPlus_lower 12606
end BstLean.Part269.N12606

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12606
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035943660017 : ℝ) ≤ wn 12606 := by
  have hn : √(12606 : ℝ) ≤ 112.276444546486 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12606 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.276444546486 ≤ 2 / √(12606 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000253792022 : ℝ) ≤ rhoBar 12606 BstLean.Part154.csC ∧
    rhoBar 12606 BstLean.Part154.csC ≤ 0.000253792414 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035943660017 : ℝ) / (1.295212 * 12606) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035943660018 : ℝ) / (1.29521 * 12606) := by gcongr
      _ ≤ (0.000253792414 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12606 BstLean.Part154.csC) ≤ 0.001015234067 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12606 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12606 BstLean.Part154.csC) (piBar (rhoBar 12606 BstLean.Part154.csC)) ≤ 0.000193848426 ∧
    cc1 (rhoBar 12606 BstLean.Part154.csC) (piBar (rhoBar 12606 BstLean.Part154.csC)) ≤ 0.000123347027 ∧
    cc2 (rhoBar 12606 BstLean.Part154.csC) ≤ 0.000071603877 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12606 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12606 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12606 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12606 BstLean.Part154.csC * nuR (rhoBar 12606 BstLean.Part154.csC)) ≤ 0.000507600931 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000253792414 : ℝ) * 0.001015234067 := by gcongr
      _ ≤ (0.000507600931 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12606 BstLean.Part154.csC) * nuR (rhoBar 12606 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001015234067 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12606 BstLean.Part154.csC) * rhoBar 12606 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000253792414 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000253792414 / 2 + 0.399 * 0.001015234067 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000193848426 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000507600931 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123347027 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000253792414 / 1.414213562 := by gcongr
      _ ≤ (0.000071603877 : ℝ) := by norm_num

end BstLean.Part269.N12606

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12606
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12606 BstLean.Part154.csC) (piBar (rhoBar 12606 BstLean.Part154.csC)) ≤ 1.62278E-7 := by
  have hr0 : 0 ≤ rhoBar 12606 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12606 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12606 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12606 BstLean.Part154.csC) (piBar (rhoBar 12606 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12606 BstLean.Part154.csC) (piBar (rhoBar 12606 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12606 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000193848426 : ℝ) ^ 2 + 0.000123347027 ^ 2 + 3 * 0.000071603877 ^ 2 +
        2 * 0.797885 * 0.000193848426 * 0.000123347027 + 2 * 0.000193848426 * 0.000071603877 +
        4 * 0.797885 * 0.000123347027 * 0.000071603877 := by gcongr
    _ ≤ (1.62278E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12606 BstLean.Part154.csC Θ ≤ 0.002649584711 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12606 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12606 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12606 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12606 BstLean.Part154.csC) (piBar (rhoBar 12606 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12606 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035943660018 * 1.62278E-7 / (0.000253792022 : ℝ) := by gcongr
    _ ≤ 0.002649584711 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12606 BstLean.Part154.csC Θ ≤ 0.002940237868 + 0.000669506779 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12606 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12606 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12606 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035943660018 : ℝ) * ((2 * Θ * 0.000253792414 +
        (6863 / 10000) * 0.000253792414 * 12606 * 0.001015234067) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002940237868 + 0.000669506779 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12606 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12606 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12606 0.011 Θ ∧ gammaRatio 12606 0.011 Θ ≤ 0.000087247269 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12606 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035943660018 : ℝ) * 0.525 / ((1 - 0.011) * 12606) := by gcongr
      _ ≤ (0.000087247269 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12606 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12606 0.011 Θ) :=
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
    badAllowance 12606 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000676285396 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12606 BstLean.Part154.csC) 1.22 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 2 (rhoBar 12606 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12606 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12606 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12606 0.011 Θ) 1.12 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 1 (gammaRatio 12606 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12606 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12606 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12606 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12606 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035943660018 : ℝ) * 12606 *
        (2.5110E-8 / 1.1045361 + 3.0670E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000676285396 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12606 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003616523264 + 0.003319091490 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12606

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12606
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12606 BstLean.Part154.csC) (piBar (rhoBar 12606 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12606 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12606 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12606 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12606 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12606 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12606 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12606 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12606 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12606 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12606 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12606 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12606 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12606 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12606 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052681756807 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12606) ≤ 0.010636581751 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12606 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035943660018)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010636581751 + 2 * 0.737676 / 12606) := by gcongr
    _ ≤ (0.052681756807 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12606 12 ≤ 0.0015 := by
  exact BstLean.Part269.S10.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12606

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12606
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560499285633 : ℝ) ≤ plow 12606 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12606) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052865646297)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001391031974) : eMP 12606 0.011 xi bn ≤ 0.001197416859 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12606 : ℝ) * (1 - 0.011))) ≤ 0.000592047729 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001391031974 / (12606 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000592047729 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000592047729 : ℝ) + 3.141593 * 0.052865646297 / (12606 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001197416859 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052865646297)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001391031974) : PiBarMP 12606 12 0.011 xi bn ≤ 0.161857167710 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12606 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037296541047 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.657216515548 : ℝ) ≤ √((12606 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.276444546485 : ℝ) ≤ √(12606 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12606) ≤ 0.124090216065 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037296541047 + 0.052865646297 * 1.772454 / (2 * (111.657216515548 : ℝ))) * (1 + 0.001197416859) +
        8 / (12606 * 112.276444546485) + 0.124090216065 := by gcongr
    _ ≤ (0.161857167710 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052865646297)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001391031974) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282607062716) :
    parallelOracle 12606 0.011 xi bn cd ≤ 0.162855157542 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12606 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12606 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560499285633 : ℝ) ≤ plow 12606 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.276444546485 : ℝ) ≤ √(12606 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282607062716 : ℝ) / (2 * 0.560499285633 * 112.276444546485)) * 0.161857167710 +
        0.282607062716 ^ 2 / (2 * 0.560499285633 * 112.276444546485) := by gcongr
    _ ≤ (0.162855157542 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052865646297) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001391031974)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282607062716) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12606 12606 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560499285633 : ℝ) ≤ plow 12606 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.276444546485 : ℝ) ≤ √(12606 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12606 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12606 Θ 1.22 ≤ 0.011811030403 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.276444546485 := by gcongr <;> linarith
      _ ≤ (0.011811030403 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12606 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12606 12606 0.011 ≤ 0.008513691900 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12606 12606 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12606 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12606 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12606 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12606 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162855157542 + 0.011811030403 + (0.008513691900 : ℝ) *
        (1 + 2 * (0.282607062716 + 0.011811030403) / (0.560499285633 * 112.276444546485))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12606]

end BstLean.Part269.N12606

/-! The original eight local profiles supply actual 12606 moment certificates. -/
namespace BstLean.Part269.N12606
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12606 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12606 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12606 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052865646297 ∧
    0 ≤ bN 12606 BstLean.Part154.csC (groupTheta g) ∧ bN 12606 BstLean.Part154.csC (groupTheta g) ≤ 0.001391031974 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12606 12606 0.011
      (momentAllowance 12606 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12606 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12606 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12606 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12606 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12606 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229925305909 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12606 0.011
      (momentAllowance 12606 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12606 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12606
/-! The actual computed-centre upper energy formula at 12606. -/
namespace BstLean.Part269.N12606
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12606

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12606
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12606)
open BstLean.Part268 (cell12606)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085769333476
  | 2 => 0.086717323931
  | 3 => 0.087664236844
  | 4 => 0.088611669271
  | 5 => 0.089561546797
  | 6 => 0.090516171525
  | 7 => 0.091478274437
  | 8 => 0.092451072138
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12606 12606 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12606 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12606

/-! Actual upper energy certificates on all 43 source endpoints at 12606. -/
namespace BstLean.Part269.N12606
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12606)
open BstLean.Part268 (cell12606)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12606 (gMinus 12606) (1 - (cell12606 i).lower) ≤ 1 ∧
    energyUpper 12606 (gMinus 12606) (BstLean.Part211.gPlus 12606)
      (finiteEnergy 12606 12606 0.011) (1 - (cell12606 i).lower) ≤
      (cell12606 i).energy := by
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
      have E := BstLean.Part269.S10.uniformEnergy10 (n := 12606) (by norm_num)
        (q := 1 - (cell12606 ⟨10,by decide⟩).lower)
        (by norm_num [cell12606]) (by norm_num [cell12606])
      exact ⟨E.1,E.2.trans (by norm_num [cell12606])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy11 (n := 12606) (by norm_num)
        (q := 1 - (cell12606 ⟨11,by decide⟩).lower)
        (by norm_num [cell12606]) (by norm_num [cell12606])
      exact ⟨E.1,E.2.trans (by norm_num [cell12606])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy12 (n := 12606) (by norm_num)
        (q := 1 - (cell12606 ⟨12,by decide⟩).lower)
        (by norm_num [cell12606]) (by norm_num [cell12606])
      exact ⟨E.1,E.2.trans (by norm_num [cell12606])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy13 (n := 12606) (by norm_num)
        (q := 1 - (cell12606 ⟨13,by decide⟩).lower)
        (by norm_num [cell12606]) (by norm_num [cell12606])
      exact ⟨E.1,E.2.trans (by norm_num [cell12606])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy14 (n := 12606) (by norm_num)
        (q := 1 - (cell12606 ⟨14,by decide⟩).lower)
        (by norm_num [cell12606]) (by norm_num [cell12606])
      exact ⟨E.1,E.2.trans (by norm_num [cell12606])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy15 (n := 12606) (by norm_num)
        (q := 1 - (cell12606 ⟨15,by decide⟩).lower)
        (by norm_num [cell12606]) (by norm_num [cell12606])
      exact ⟨E.1,E.2.trans (by norm_num [cell12606])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy16 (n := 12606) (by norm_num)
        (q := 1 - (cell12606 ⟨16,by decide⟩).lower)
        (by norm_num [cell12606]) (by norm_num [cell12606])
      exact ⟨E.1,E.2.trans (by norm_num [cell12606])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy17 (n := 12606) (by norm_num)
        (q := 1 - (cell12606 ⟨17,by decide⟩).lower)
        (by norm_num [cell12606]) (by norm_num [cell12606])
      exact ⟨E.1,E.2.trans (by norm_num [cell12606])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy18 (n := 12606) (by norm_num)
        (q := 1 - (cell12606 ⟨18,by decide⟩).lower)
        (by norm_num [cell12606]) (by norm_num [cell12606])
      exact ⟨E.1,E.2.trans (by norm_num [cell12606])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy19 (n := 12606) (by norm_num)
        (q := 1 - (cell12606 ⟨19,by decide⟩).lower)
        (by norm_num [cell12606]) (by norm_num [cell12606])
      exact ⟨E.1,E.2.trans (by norm_num [cell12606])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy20 (n := 12606) (by norm_num)
        (q := 1 - (cell12606 ⟨20,by decide⟩).lower)
        (by norm_num [cell12606]) (by norm_num [cell12606])
      exact ⟨E.1,E.2.trans (by norm_num [cell12606])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy21 (n := 12606) (by norm_num)
        (q := 1 - (cell12606 ⟨21,by decide⟩).lower)
        (by norm_num [cell12606]) (by norm_num [cell12606])
      exact ⟨E.1,E.2.trans (by norm_num [cell12606])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy22 (n := 12606) (by norm_num)
        (q := 1 - (cell12606 ⟨22,by decide⟩).lower)
        (by norm_num [cell12606]) (by norm_num [cell12606])
      exact ⟨E.1,E.2.trans (by norm_num [cell12606])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy23 (n := 12606) (by norm_num)
        (q := 1 - (cell12606 ⟨23,by decide⟩).lower)
        (by norm_num [cell12606]) (by norm_num [cell12606])
      exact ⟨E.1,E.2.trans (by norm_num [cell12606])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy24 (n := 12606) (by norm_num)
        (q := 1 - (cell12606 ⟨24,by decide⟩).lower)
        (by norm_num [cell12606]) (by norm_num [cell12606])
      exact ⟨E.1,E.2.trans (by norm_num [cell12606])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy25 (n := 12606) (by norm_num)
        (q := 1 - (cell12606 ⟨25,by decide⟩).lower)
        (by norm_num [cell12606]) (by norm_num [cell12606])
      exact ⟨E.1,E.2.trans (by norm_num [cell12606])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy26 (n := 12606) (by norm_num)
        (q := 1 - (cell12606 ⟨26,by decide⟩).lower)
        (by norm_num [cell12606]) (by norm_num [cell12606])
      exact ⟨E.1,E.2.trans (by norm_num [cell12606])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy27 (n := 12606) (by norm_num)
        (q := 1 - (cell12606 ⟨27,by decide⟩).lower)
        (by norm_num [cell12606]) (by norm_num [cell12606])
      exact ⟨E.1,E.2.trans (by norm_num [cell12606])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy28 (n := 12606) (by norm_num)
        (q := 1 - (cell12606 ⟨28,by decide⟩).lower)
        (by norm_num [cell12606]) (by norm_num [cell12606])
      exact ⟨E.1,E.2.trans (by norm_num [cell12606])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy29 (n := 12606) (by norm_num)
        (q := 1 - (cell12606 ⟨29,by decide⟩).lower)
        (by norm_num [cell12606]) (by norm_num [cell12606])
      exact ⟨E.1,E.2.trans (by norm_num [cell12606])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy30 (n := 12606) (by norm_num)
        (q := 1 - (cell12606 ⟨30,by decide⟩).lower)
        (by norm_num [cell12606]) (by norm_num [cell12606])
      exact ⟨E.1,E.2.trans (by norm_num [cell12606])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy31 (n := 12606) (by norm_num)
        (q := 1 - (cell12606 ⟨31,by decide⟩).lower)
        (by norm_num [cell12606]) (by norm_num [cell12606])
      exact ⟨E.1,E.2.trans (by norm_num [cell12606])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy32 (n := 12606) (by norm_num)
        (q := 1 - (cell12606 ⟨32,by decide⟩).lower)
        (by norm_num [cell12606]) (by norm_num [cell12606])
      exact ⟨E.1,E.2.trans (by norm_num [cell12606])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy33 (n := 12606) (by norm_num)
        (q := 1 - (cell12606 ⟨33,by decide⟩).lower)
        (by norm_num [cell12606]) (by norm_num [cell12606])
      exact ⟨E.1,E.2.trans (by norm_num [cell12606])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy34 (n := 12606) (by norm_num)
        (q := 1 - (cell12606 ⟨34,by decide⟩).lower)
        (by norm_num [cell12606]) (by norm_num [cell12606])
      exact ⟨E.1,E.2.trans (by norm_num [cell12606])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy35 (n := 12606) (by norm_num)
        (q := 1 - (cell12606 ⟨35,by decide⟩).lower)
        (by norm_num [cell12606]) (by norm_num [cell12606])
      exact ⟨E.1,E.2.trans (by norm_num [cell12606])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy36 (n := 12606) (by norm_num)
        (q := 1 - (cell12606 ⟨36,by decide⟩).lower)
        (by norm_num [cell12606]) (by norm_num [cell12606])
      exact ⟨E.1,E.2.trans (by norm_num [cell12606])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy37 (n := 12606) (by norm_num)
        (q := 1 - (cell12606 ⟨37,by decide⟩).lower)
        (by norm_num [cell12606]) (by norm_num [cell12606])
      exact ⟨E.1,E.2.trans (by norm_num [cell12606])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy38 (n := 12606) (by norm_num)
        (q := 1 - (cell12606 ⟨38,by decide⟩).lower)
        (by norm_num [cell12606]) (by norm_num [cell12606])
      exact ⟨E.1,E.2.trans (by norm_num [cell12606])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy39 (n := 12606) (by norm_num)
        (q := 1 - (cell12606 ⟨39,by decide⟩).lower)
        (by norm_num [cell12606]) (by norm_num [cell12606])
      exact ⟨E.1,E.2.trans (by norm_num [cell12606])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy40 (n := 12606) (by norm_num)
        (q := 1 - (cell12606 ⟨40,by decide⟩).lower)
        (by norm_num [cell12606]) (by norm_num [cell12606])
      exact ⟨E.1,E.2.trans (by norm_num [cell12606])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy41 (n := 12606) (by norm_num)
        (q := 1 - (cell12606 ⟨41,by decide⟩).lower)
        (by norm_num [cell12606]) (by norm_num [cell12606])
      exact ⟨E.1,E.2.trans (by norm_num [cell12606])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy42 (n := 12606) (by norm_num)
        (q := 1 - (cell12606 ⟨42,by decide⟩).lower)
        (by norm_num [cell12606]) (by norm_num [cell12606])
      exact ⟨E.1,E.2.trans (by norm_num [cell12606])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy43 (n := 12606) (by norm_num)
        (q := 1 - (cell12606 ⟨43,by decide⟩).lower)
        (by norm_num [cell12606]) (by norm_num [cell12606])
      exact ⟨E.1,E.2.trans (by norm_num [cell12606])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy44 (n := 12606) (by norm_num)
        (q := 1 - (cell12606 ⟨44,by decide⟩).lower)
        (by norm_num [cell12606]) (by norm_num [cell12606])
      exact ⟨E.1,E.2.trans (by norm_num [cell12606])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy45 (n := 12606) (by norm_num)
        (q := 1 - (cell12606 ⟨45,by decide⟩).lower)
        (by norm_num [cell12606]) (by norm_num [cell12606])
      exact ⟨E.1,E.2.trans (by norm_num [cell12606])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy46 (n := 12606) (by norm_num)
        (q := 1 - (cell12606 ⟨46,by decide⟩).lower)
        (by norm_num [cell12606]) (by norm_num [cell12606])
      exact ⟨E.1,E.2.trans (by norm_num [cell12606])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy47 (n := 12606) (by norm_num)
        (q := 1 - (cell12606 ⟨47,by decide⟩).lower)
        (by norm_num [cell12606]) (by norm_num [cell12606])
      exact ⟨E.1,E.2.trans (by norm_num [cell12606])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy48 (n := 12606) (by norm_num)
        (q := 1 - (cell12606 ⟨48,by decide⟩).lower)
        (by norm_num [cell12606]) (by norm_num [cell12606])
      exact ⟨E.1,E.2.trans (by norm_num [cell12606])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy49 (n := 12606) (by norm_num)
        (q := 1 - (cell12606 ⟨49,by decide⟩).lower)
        (by norm_num [cell12606]) (by norm_num [cell12606])
      exact ⟨E.1,E.2.trans (by norm_num [cell12606])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy50 (n := 12606) (by norm_num)
        (q := 1 - (cell12606 ⟨50,by decide⟩).lower)
        (by norm_num [cell12606]) (by norm_num [cell12606])
      exact ⟨E.1,E.2.trans (by norm_num [cell12606])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy51 (n := 12606) (by norm_num)
        (q := 1 - (cell12606 ⟨51,by decide⟩).lower)
        (by norm_num [cell12606]) (by norm_num [cell12606])
      exact ⟨E.1,E.2.trans (by norm_num [cell12606])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy52 (n := 12606) (by norm_num)
        (q := 1 - (cell12606 ⟨52,by decide⟩).lower)
        (by norm_num [cell12606]) (by norm_num [cell12606])
      exact ⟨E.1,E.2.trans (by norm_num [cell12606])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12606

/-! Source-cell containment and simple scalar guards at 12606. -/
namespace BstLean.Part269.N12606
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12606)
open BstLean.Part268 (cell12606)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12606 ⟨10,by decide⟩).lower ∧ (cell12606 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12606 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12606 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12606 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12606 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12606 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12606,cell12606,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12606 ⟨11,by decide⟩).lower ∧ (cell12606 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12606 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12606 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12606 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12606 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12606 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12606,cell12606,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12606 ⟨12,by decide⟩).lower ∧ (cell12606 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12606 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12606 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12606 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12606 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12606 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12606,cell12606,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12606 ⟨13,by decide⟩).lower ∧ (cell12606 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12606 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12606 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12606 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12606 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12606 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12606,cell12606,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12606 ⟨14,by decide⟩).lower ∧ (cell12606 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12606 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12606 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12606 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12606 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12606 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12606,cell12606,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12606 ⟨15,by decide⟩).lower ∧ (cell12606 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12606 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12606 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12606 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12606 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12606 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12606,cell12606,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12606 ⟨16,by decide⟩).lower ∧ (cell12606 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12606 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12606 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12606 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12606 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12606 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12606,cell12606,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12606 ⟨17,by decide⟩).lower ∧ (cell12606 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12606 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12606 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12606 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12606 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12606 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12606,cell12606,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12606 ⟨18,by decide⟩).lower ∧ (cell12606 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12606 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12606 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12606 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12606 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12606 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12606,cell12606,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12606 ⟨19,by decide⟩).lower ∧ (cell12606 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12606 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12606 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12606 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12606 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12606 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12606,cell12606,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12606 ⟨20,by decide⟩).lower ∧ (cell12606 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12606 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12606 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12606 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12606 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12606 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12606,cell12606,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12606 ⟨21,by decide⟩).lower ∧ (cell12606 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12606 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12606 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12606 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12606 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12606 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12606,cell12606,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12606 ⟨22,by decide⟩).lower ∧ (cell12606 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12606 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12606 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12606 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12606 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12606 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12606,cell12606,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12606 ⟨23,by decide⟩).lower ∧ (cell12606 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12606 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12606 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12606 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12606 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12606 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12606,cell12606,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12606 ⟨24,by decide⟩).lower ∧ (cell12606 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12606 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12606 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12606 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12606 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12606 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12606,cell12606,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12606 ⟨25,by decide⟩).lower ∧ (cell12606 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12606 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12606 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12606 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12606 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12606 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12606,cell12606,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12606 ⟨26,by decide⟩).lower ∧ (cell12606 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12606 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12606 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12606 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12606 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12606 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12606,cell12606,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12606 ⟨27,by decide⟩).lower ∧ (cell12606 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12606 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12606 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12606 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12606 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12606 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12606,cell12606,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12606 ⟨28,by decide⟩).lower ∧ (cell12606 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12606 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12606 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12606 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12606 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12606 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12606,cell12606,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12606 ⟨29,by decide⟩).lower ∧ (cell12606 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12606 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12606 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12606 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12606 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12606 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12606,cell12606,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12606 ⟨30,by decide⟩).lower ∧ (cell12606 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12606 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12606 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12606 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12606 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12606 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12606,cell12606,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12606 ⟨31,by decide⟩).lower ∧ (cell12606 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12606 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12606 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12606 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12606 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12606 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12606,cell12606,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12606 ⟨32,by decide⟩).lower ∧ (cell12606 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12606 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12606 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12606 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12606 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12606 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12606,cell12606,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12606 ⟨33,by decide⟩).lower ∧ (cell12606 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12606 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12606 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12606 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12606 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12606 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12606,cell12606,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12606 ⟨34,by decide⟩).lower ∧ (cell12606 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12606 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12606 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12606 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12606 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12606 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12606,cell12606,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12606 ⟨35,by decide⟩).lower ∧ (cell12606 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12606 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12606 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12606 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12606 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12606 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12606,cell12606,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12606 ⟨36,by decide⟩).lower ∧ (cell12606 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12606 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12606 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12606 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12606 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12606 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12606,cell12606,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12606 ⟨37,by decide⟩).lower ∧ (cell12606 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12606 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12606 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12606 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12606 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12606 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12606,cell12606,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12606 ⟨38,by decide⟩).lower ∧ (cell12606 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12606 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12606 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12606 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12606 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12606 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12606,cell12606,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12606 ⟨39,by decide⟩).lower ∧ (cell12606 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12606 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12606 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12606 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12606 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12606 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12606,cell12606,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12606 ⟨40,by decide⟩).lower ∧ (cell12606 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12606 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12606 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12606 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12606 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12606 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12606,cell12606,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12606 ⟨41,by decide⟩).lower ∧ (cell12606 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12606 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12606 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12606 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12606 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12606 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12606,cell12606,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12606 ⟨42,by decide⟩).lower ∧ (cell12606 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12606 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12606 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12606 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12606 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12606 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12606,cell12606,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12606 ⟨43,by decide⟩).lower ∧ (cell12606 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12606 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12606 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12606 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12606 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12606 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12606,cell12606,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12606 ⟨44,by decide⟩).lower ∧ (cell12606 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12606 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12606 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12606 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12606 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12606 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12606,cell12606,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12606 ⟨45,by decide⟩).lower ∧ (cell12606 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12606 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12606 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12606 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12606 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12606 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12606,cell12606,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12606 ⟨46,by decide⟩).lower ∧ (cell12606 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12606 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12606 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12606 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12606 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12606 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12606,cell12606,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12606 ⟨47,by decide⟩).lower ∧ (cell12606 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12606 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12606 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12606 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12606 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12606 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12606,cell12606,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12606 ⟨48,by decide⟩).lower ∧ (cell12606 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12606 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12606 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12606 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12606 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12606 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12606,cell12606,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12606 ⟨49,by decide⟩).lower ∧ (cell12606 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12606 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12606 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12606 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12606 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12606 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12606,cell12606,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12606 ⟨50,by decide⟩).lower ∧ (cell12606 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12606 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12606 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12606 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12606 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12606 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12606,cell12606,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12606 ⟨51,by decide⟩).lower ∧ (cell12606 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12606 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12606 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12606 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12606 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12606 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12606,cell12606,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12606 ⟨52,by decide⟩).lower ∧ (cell12606 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12606 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12606 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12606 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12606 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12606 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12606,cell12606,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12606 i).lower ∧
    (cell12606 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12606 i).upper ≤ (0.532 : ℝ) ∧
    (cell12606 i).centre ≤ (0.1 : ℝ) ∧ (cell12606 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12606 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12606 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12606

/-! The local source numeric instances at 12606 have no network premises. -/
namespace BstLean.Part269.N12606
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12606)
open BstLean.Part268 (cell12606)

noncomputable def sourceNumerics12606 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12606 (cell12606 i)
      scalarRow12606.M scalarRow12606.H scalarRow12606.xi := by
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
    energy_allowance := scalarRow12606.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12606]
    centre_nonneg := (scalarRow12606.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D10.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12606])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12606
/-! Actual 12607 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12607
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12607 ≤ (1.035942221862 : ℝ) := by
  have hr : (112.280897752021 : ℝ) ≤ √(12607 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.280897752021 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12607 12607 (11 / 1000) ≤
    (0.008513354234 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12607) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.280897752021 : ℝ) ≤ √(12607 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12607)
  have hdiv : K / √(12607 : ℝ) ≤ K / 112.280897752021 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.280897752021 ≤ (0.008513354234 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12607.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12607 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12607 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12607 := gPlus_lower 12607
end BstLean.Part269.N12607

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12607
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035942221861 : ℝ) ≤ wn 12607 := by
  have hn : √(12607 : ℝ) ≤ 112.280897752022 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12607 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.280897752022 ≤ 2 / √(12607 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000253771538 : ℝ) ≤ rhoBar 12607 BstLean.Part154.csC ∧
    rhoBar 12607 BstLean.Part154.csC ≤ 0.000253771931 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035942221861 : ℝ) / (1.295212 * 12607) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035942221862 : ℝ) / (1.29521 * 12607) := by gcongr
      _ ≤ (0.000253771931 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12607 BstLean.Part154.csC) ≤ 0.001015152125 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12607 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12607 BstLean.Part154.csC) (piBar (rhoBar 12607 BstLean.Part154.csC)) ≤ 0.000193832781 ∧
    cc1 (rhoBar 12607 BstLean.Part154.csC) (piBar (rhoBar 12607 BstLean.Part154.csC)) ≤ 0.000123337071 ∧
    cc2 (rhoBar 12607 BstLean.Part154.csC) ≤ 0.000071598098 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12607 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12607 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12607 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12607 BstLean.Part154.csC * nuR (rhoBar 12607 BstLean.Part154.csC)) ≤ 0.000507559962 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000253771931 : ℝ) * 0.001015152125 := by gcongr
      _ ≤ (0.000507559962 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12607 BstLean.Part154.csC) * nuR (rhoBar 12607 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001015152125 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12607 BstLean.Part154.csC) * rhoBar 12607 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000253771931 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000253771931 / 2 + 0.399 * 0.001015152125 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000193832781 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000507559962 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123337071 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000253771931 / 1.414213562 := by gcongr
      _ ≤ (0.000071598098 : ℝ) := by norm_num

end BstLean.Part269.N12607

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12607
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12607 BstLean.Part154.csC) (piBar (rhoBar 12607 BstLean.Part154.csC)) ≤ 1.62252E-7 := by
  have hr0 : 0 ≤ rhoBar 12607 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12607 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12607 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12607 BstLean.Part154.csC) (piBar (rhoBar 12607 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12607 BstLean.Part154.csC) (piBar (rhoBar 12607 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12607 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000193832781 : ℝ) ^ 2 + 0.000123337071 ^ 2 + 3 * 0.000071598098 ^ 2 +
        2 * 0.797885 * 0.000193832781 * 0.000123337071 + 2 * 0.000193832781 * 0.000071598098 +
        4 * 0.797885 * 0.000123337071 * 0.000071598098 := by gcongr
    _ ≤ (1.62252E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12607 BstLean.Part154.csC Θ ≤ 0.002649370355 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12607 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12607 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12607 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12607 BstLean.Part154.csC) (piBar (rhoBar 12607 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12607 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035942221862 * 1.62252E-7 / (0.000253771538 : ℝ) := by gcongr
    _ ≤ 0.002649370355 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12607 BstLean.Part154.csC Θ ≤ 0.002939992396 + 0.000669451815 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12607 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12607 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12607 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035942221862 : ℝ) * ((2 * Θ * 0.000253771931 +
        (6863 / 10000) * 0.000253771931 * 12607 * 0.001015152125) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002939992396 + 0.000669451815 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12607 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12607 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12607 0.011 Θ ∧ gammaRatio 12607 0.011 Θ ≤ 0.000087240228 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12607 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035942221862 : ℝ) * 0.525 / ((1 - 0.011) * 12607) := by gcongr
      _ ≤ (0.000087240228 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12607 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12607 0.011 Θ) :=
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
    badAllowance 12607 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000676285396 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12607 BstLean.Part154.csC) 1.22 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 2 (rhoBar 12607 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12607 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12607 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12607 0.011 Θ) 1.12 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 1 (gammaRatio 12607 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12607 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12607 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12607 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12607 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035942221862 : ℝ) * 12607 *
        (2.5110E-8 / 1.1045361 + 3.0670E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000676285396 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12607 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003616277792 + 0.003318822170 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12607

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12607
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12607 BstLean.Part154.csC) (piBar (rhoBar 12607 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12607 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12607 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12607 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12607 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12607 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12607 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12607 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12607 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12607 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12607 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12607 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12607 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12607 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12607 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052679644640 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12607) ≤ 0.010636159890 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12607 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035942221862)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010636159890 + 2 * 0.737676 / 12607) := by gcongr
    _ ≤ (0.052679644640 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12607 12 ≤ 0.0015 := by
  exact BstLean.Part269.S10.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12607

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12607
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560499331530 : ℝ) ≤ plow 12607 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12607) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052865259432)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001390919437) : eMP 12607 0.011 xi bn ≤ 0.001197320846 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12607 : ℝ) * (1 - 0.011))) ≤ 0.000592000300 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001390919437 / (12607 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000592000300 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000592000300 : ℝ) + 3.141593 * 0.052865259432 / (12607 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001197320846 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052865259432)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001390919437) : PiBarMP 12607 12 0.011 xi bn ≤ 0.161850711586 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12607 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037295032337 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.661645160726 : ℝ) ≤ √((12607 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.280897752021 : ℝ) ≤ √(12607 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12607) ≤ 0.124085294487 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037295032337 + 0.052865259432 * 1.772454 / (2 * (111.661645160726 : ℝ))) * (1 + 0.001197320846) +
        8 / (12607 * 112.280897752021) + 0.124085294487 := by gcongr
    _ ≤ (0.161850711586 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052865259432)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001390919437) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282604109263) :
    parallelOracle 12607 0.011 xi bn cd ≤ 0.162848630199 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12607 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12607 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560499331530 : ℝ) ≤ plow 12607 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.280897752021 : ℝ) ≤ √(12607 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282604109263 : ℝ) / (2 * 0.560499331530 * 112.280897752021)) * 0.161850711586 +
        0.282604109263 ^ 2 / (2 * 0.560499331530 * 112.280897752021) := by gcongr
    _ ≤ (0.162848630199 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052865259432) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001390919437)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282604109263) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12607 12607 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560499331530 : ℝ) ≤ plow 12607 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.280897752021 : ℝ) ≤ √(12607 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12607 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12607 Θ 1.22 ≤ 0.011810561962 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.280897752021 := by gcongr <;> linarith
      _ ≤ (0.011810561962 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12607 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12607 12607 0.011 ≤ 0.008513354234 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12607 12607 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12607 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12607 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12607 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12607 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162848630199 + 0.011810561962 + (0.008513354234 : ℝ) *
        (1 + 2 * (0.282604109263 + 0.011810561962) / (0.560499331530 * 112.280897752021))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12607]

end BstLean.Part269.N12607

/-! The original eight local profiles supply actual 12607 moment certificates. -/
namespace BstLean.Part269.N12607
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12607 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12607 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12607 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052865259432 ∧
    0 ≤ bN 12607 BstLean.Part154.csC (groupTheta g) ∧ bN 12607 BstLean.Part154.csC (groupTheta g) ≤ 0.001390919437 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12607 12607 0.011
      (momentAllowance 12607 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12607 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12607 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12607 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12607 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12607 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229924464623 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12607 0.011
      (momentAllowance 12607 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12607 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12607
/-! The actual computed-centre upper energy formula at 12607. -/
namespace BstLean.Part269.N12607
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12607

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12607
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12607)
open BstLean.Part268 (cell12607)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085766310834
  | 2 => 0.086714243288
  | 3 => 0.087661089344
  | 4 => 0.088608444050
  | 5 => 0.089558230629
  | 6 => 0.090512748432
  | 7 => 0.091474725251
  | 8 => 0.092447374019
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12607 12607 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12607 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12607

/-! Actual upper energy certificates on all 43 source endpoints at 12607. -/
namespace BstLean.Part269.N12607
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12607)
open BstLean.Part268 (cell12607)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12607 (gMinus 12607) (1 - (cell12607 i).lower) ≤ 1 ∧
    energyUpper 12607 (gMinus 12607) (BstLean.Part211.gPlus 12607)
      (finiteEnergy 12607 12607 0.011) (1 - (cell12607 i).lower) ≤
      (cell12607 i).energy := by
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
      have E := BstLean.Part269.S10.uniformEnergy10 (n := 12607) (by norm_num)
        (q := 1 - (cell12607 ⟨10,by decide⟩).lower)
        (by norm_num [cell12607]) (by norm_num [cell12607])
      exact ⟨E.1,E.2.trans (by norm_num [cell12607])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy11 (n := 12607) (by norm_num)
        (q := 1 - (cell12607 ⟨11,by decide⟩).lower)
        (by norm_num [cell12607]) (by norm_num [cell12607])
      exact ⟨E.1,E.2.trans (by norm_num [cell12607])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy12 (n := 12607) (by norm_num)
        (q := 1 - (cell12607 ⟨12,by decide⟩).lower)
        (by norm_num [cell12607]) (by norm_num [cell12607])
      exact ⟨E.1,E.2.trans (by norm_num [cell12607])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy13 (n := 12607) (by norm_num)
        (q := 1 - (cell12607 ⟨13,by decide⟩).lower)
        (by norm_num [cell12607]) (by norm_num [cell12607])
      exact ⟨E.1,E.2.trans (by norm_num [cell12607])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy14 (n := 12607) (by norm_num)
        (q := 1 - (cell12607 ⟨14,by decide⟩).lower)
        (by norm_num [cell12607]) (by norm_num [cell12607])
      exact ⟨E.1,E.2.trans (by norm_num [cell12607])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy15 (n := 12607) (by norm_num)
        (q := 1 - (cell12607 ⟨15,by decide⟩).lower)
        (by norm_num [cell12607]) (by norm_num [cell12607])
      exact ⟨E.1,E.2.trans (by norm_num [cell12607])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy16 (n := 12607) (by norm_num)
        (q := 1 - (cell12607 ⟨16,by decide⟩).lower)
        (by norm_num [cell12607]) (by norm_num [cell12607])
      exact ⟨E.1,E.2.trans (by norm_num [cell12607])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy17 (n := 12607) (by norm_num)
        (q := 1 - (cell12607 ⟨17,by decide⟩).lower)
        (by norm_num [cell12607]) (by norm_num [cell12607])
      exact ⟨E.1,E.2.trans (by norm_num [cell12607])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy18 (n := 12607) (by norm_num)
        (q := 1 - (cell12607 ⟨18,by decide⟩).lower)
        (by norm_num [cell12607]) (by norm_num [cell12607])
      exact ⟨E.1,E.2.trans (by norm_num [cell12607])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy19 (n := 12607) (by norm_num)
        (q := 1 - (cell12607 ⟨19,by decide⟩).lower)
        (by norm_num [cell12607]) (by norm_num [cell12607])
      exact ⟨E.1,E.2.trans (by norm_num [cell12607])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy20 (n := 12607) (by norm_num)
        (q := 1 - (cell12607 ⟨20,by decide⟩).lower)
        (by norm_num [cell12607]) (by norm_num [cell12607])
      exact ⟨E.1,E.2.trans (by norm_num [cell12607])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy21 (n := 12607) (by norm_num)
        (q := 1 - (cell12607 ⟨21,by decide⟩).lower)
        (by norm_num [cell12607]) (by norm_num [cell12607])
      exact ⟨E.1,E.2.trans (by norm_num [cell12607])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy22 (n := 12607) (by norm_num)
        (q := 1 - (cell12607 ⟨22,by decide⟩).lower)
        (by norm_num [cell12607]) (by norm_num [cell12607])
      exact ⟨E.1,E.2.trans (by norm_num [cell12607])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy23 (n := 12607) (by norm_num)
        (q := 1 - (cell12607 ⟨23,by decide⟩).lower)
        (by norm_num [cell12607]) (by norm_num [cell12607])
      exact ⟨E.1,E.2.trans (by norm_num [cell12607])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy24 (n := 12607) (by norm_num)
        (q := 1 - (cell12607 ⟨24,by decide⟩).lower)
        (by norm_num [cell12607]) (by norm_num [cell12607])
      exact ⟨E.1,E.2.trans (by norm_num [cell12607])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy25 (n := 12607) (by norm_num)
        (q := 1 - (cell12607 ⟨25,by decide⟩).lower)
        (by norm_num [cell12607]) (by norm_num [cell12607])
      exact ⟨E.1,E.2.trans (by norm_num [cell12607])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy26 (n := 12607) (by norm_num)
        (q := 1 - (cell12607 ⟨26,by decide⟩).lower)
        (by norm_num [cell12607]) (by norm_num [cell12607])
      exact ⟨E.1,E.2.trans (by norm_num [cell12607])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy27 (n := 12607) (by norm_num)
        (q := 1 - (cell12607 ⟨27,by decide⟩).lower)
        (by norm_num [cell12607]) (by norm_num [cell12607])
      exact ⟨E.1,E.2.trans (by norm_num [cell12607])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy28 (n := 12607) (by norm_num)
        (q := 1 - (cell12607 ⟨28,by decide⟩).lower)
        (by norm_num [cell12607]) (by norm_num [cell12607])
      exact ⟨E.1,E.2.trans (by norm_num [cell12607])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy29 (n := 12607) (by norm_num)
        (q := 1 - (cell12607 ⟨29,by decide⟩).lower)
        (by norm_num [cell12607]) (by norm_num [cell12607])
      exact ⟨E.1,E.2.trans (by norm_num [cell12607])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy30 (n := 12607) (by norm_num)
        (q := 1 - (cell12607 ⟨30,by decide⟩).lower)
        (by norm_num [cell12607]) (by norm_num [cell12607])
      exact ⟨E.1,E.2.trans (by norm_num [cell12607])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy31 (n := 12607) (by norm_num)
        (q := 1 - (cell12607 ⟨31,by decide⟩).lower)
        (by norm_num [cell12607]) (by norm_num [cell12607])
      exact ⟨E.1,E.2.trans (by norm_num [cell12607])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy32 (n := 12607) (by norm_num)
        (q := 1 - (cell12607 ⟨32,by decide⟩).lower)
        (by norm_num [cell12607]) (by norm_num [cell12607])
      exact ⟨E.1,E.2.trans (by norm_num [cell12607])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy33 (n := 12607) (by norm_num)
        (q := 1 - (cell12607 ⟨33,by decide⟩).lower)
        (by norm_num [cell12607]) (by norm_num [cell12607])
      exact ⟨E.1,E.2.trans (by norm_num [cell12607])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy34 (n := 12607) (by norm_num)
        (q := 1 - (cell12607 ⟨34,by decide⟩).lower)
        (by norm_num [cell12607]) (by norm_num [cell12607])
      exact ⟨E.1,E.2.trans (by norm_num [cell12607])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy35 (n := 12607) (by norm_num)
        (q := 1 - (cell12607 ⟨35,by decide⟩).lower)
        (by norm_num [cell12607]) (by norm_num [cell12607])
      exact ⟨E.1,E.2.trans (by norm_num [cell12607])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy36 (n := 12607) (by norm_num)
        (q := 1 - (cell12607 ⟨36,by decide⟩).lower)
        (by norm_num [cell12607]) (by norm_num [cell12607])
      exact ⟨E.1,E.2.trans (by norm_num [cell12607])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy37 (n := 12607) (by norm_num)
        (q := 1 - (cell12607 ⟨37,by decide⟩).lower)
        (by norm_num [cell12607]) (by norm_num [cell12607])
      exact ⟨E.1,E.2.trans (by norm_num [cell12607])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy38 (n := 12607) (by norm_num)
        (q := 1 - (cell12607 ⟨38,by decide⟩).lower)
        (by norm_num [cell12607]) (by norm_num [cell12607])
      exact ⟨E.1,E.2.trans (by norm_num [cell12607])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy39 (n := 12607) (by norm_num)
        (q := 1 - (cell12607 ⟨39,by decide⟩).lower)
        (by norm_num [cell12607]) (by norm_num [cell12607])
      exact ⟨E.1,E.2.trans (by norm_num [cell12607])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy40 (n := 12607) (by norm_num)
        (q := 1 - (cell12607 ⟨40,by decide⟩).lower)
        (by norm_num [cell12607]) (by norm_num [cell12607])
      exact ⟨E.1,E.2.trans (by norm_num [cell12607])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy41 (n := 12607) (by norm_num)
        (q := 1 - (cell12607 ⟨41,by decide⟩).lower)
        (by norm_num [cell12607]) (by norm_num [cell12607])
      exact ⟨E.1,E.2.trans (by norm_num [cell12607])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy42 (n := 12607) (by norm_num)
        (q := 1 - (cell12607 ⟨42,by decide⟩).lower)
        (by norm_num [cell12607]) (by norm_num [cell12607])
      exact ⟨E.1,E.2.trans (by norm_num [cell12607])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy43 (n := 12607) (by norm_num)
        (q := 1 - (cell12607 ⟨43,by decide⟩).lower)
        (by norm_num [cell12607]) (by norm_num [cell12607])
      exact ⟨E.1,E.2.trans (by norm_num [cell12607])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy44 (n := 12607) (by norm_num)
        (q := 1 - (cell12607 ⟨44,by decide⟩).lower)
        (by norm_num [cell12607]) (by norm_num [cell12607])
      exact ⟨E.1,E.2.trans (by norm_num [cell12607])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy45 (n := 12607) (by norm_num)
        (q := 1 - (cell12607 ⟨45,by decide⟩).lower)
        (by norm_num [cell12607]) (by norm_num [cell12607])
      exact ⟨E.1,E.2.trans (by norm_num [cell12607])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy46 (n := 12607) (by norm_num)
        (q := 1 - (cell12607 ⟨46,by decide⟩).lower)
        (by norm_num [cell12607]) (by norm_num [cell12607])
      exact ⟨E.1,E.2.trans (by norm_num [cell12607])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy47 (n := 12607) (by norm_num)
        (q := 1 - (cell12607 ⟨47,by decide⟩).lower)
        (by norm_num [cell12607]) (by norm_num [cell12607])
      exact ⟨E.1,E.2.trans (by norm_num [cell12607])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy48 (n := 12607) (by norm_num)
        (q := 1 - (cell12607 ⟨48,by decide⟩).lower)
        (by norm_num [cell12607]) (by norm_num [cell12607])
      exact ⟨E.1,E.2.trans (by norm_num [cell12607])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy49 (n := 12607) (by norm_num)
        (q := 1 - (cell12607 ⟨49,by decide⟩).lower)
        (by norm_num [cell12607]) (by norm_num [cell12607])
      exact ⟨E.1,E.2.trans (by norm_num [cell12607])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy50 (n := 12607) (by norm_num)
        (q := 1 - (cell12607 ⟨50,by decide⟩).lower)
        (by norm_num [cell12607]) (by norm_num [cell12607])
      exact ⟨E.1,E.2.trans (by norm_num [cell12607])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy51 (n := 12607) (by norm_num)
        (q := 1 - (cell12607 ⟨51,by decide⟩).lower)
        (by norm_num [cell12607]) (by norm_num [cell12607])
      exact ⟨E.1,E.2.trans (by norm_num [cell12607])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy52 (n := 12607) (by norm_num)
        (q := 1 - (cell12607 ⟨52,by decide⟩).lower)
        (by norm_num [cell12607]) (by norm_num [cell12607])
      exact ⟨E.1,E.2.trans (by norm_num [cell12607])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12607

/-! Source-cell containment and simple scalar guards at 12607. -/
namespace BstLean.Part269.N12607
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12607)
open BstLean.Part268 (cell12607)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12607 ⟨10,by decide⟩).lower ∧ (cell12607 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12607 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12607 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12607 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12607 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12607 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12607,cell12607,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12607 ⟨11,by decide⟩).lower ∧ (cell12607 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12607 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12607 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12607 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12607 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12607 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12607,cell12607,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12607 ⟨12,by decide⟩).lower ∧ (cell12607 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12607 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12607 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12607 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12607 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12607 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12607,cell12607,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12607 ⟨13,by decide⟩).lower ∧ (cell12607 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12607 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12607 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12607 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12607 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12607 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12607,cell12607,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12607 ⟨14,by decide⟩).lower ∧ (cell12607 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12607 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12607 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12607 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12607 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12607 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12607,cell12607,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12607 ⟨15,by decide⟩).lower ∧ (cell12607 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12607 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12607 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12607 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12607 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12607 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12607,cell12607,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12607 ⟨16,by decide⟩).lower ∧ (cell12607 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12607 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12607 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12607 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12607 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12607 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12607,cell12607,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12607 ⟨17,by decide⟩).lower ∧ (cell12607 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12607 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12607 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12607 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12607 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12607 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12607,cell12607,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12607 ⟨18,by decide⟩).lower ∧ (cell12607 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12607 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12607 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12607 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12607 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12607 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12607,cell12607,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12607 ⟨19,by decide⟩).lower ∧ (cell12607 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12607 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12607 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12607 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12607 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12607 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12607,cell12607,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12607 ⟨20,by decide⟩).lower ∧ (cell12607 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12607 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12607 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12607 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12607 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12607 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12607,cell12607,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12607 ⟨21,by decide⟩).lower ∧ (cell12607 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12607 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12607 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12607 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12607 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12607 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12607,cell12607,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12607 ⟨22,by decide⟩).lower ∧ (cell12607 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12607 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12607 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12607 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12607 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12607 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12607,cell12607,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12607 ⟨23,by decide⟩).lower ∧ (cell12607 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12607 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12607 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12607 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12607 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12607 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12607,cell12607,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12607 ⟨24,by decide⟩).lower ∧ (cell12607 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12607 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12607 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12607 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12607 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12607 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12607,cell12607,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12607 ⟨25,by decide⟩).lower ∧ (cell12607 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12607 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12607 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12607 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12607 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12607 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12607,cell12607,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12607 ⟨26,by decide⟩).lower ∧ (cell12607 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12607 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12607 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12607 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12607 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12607 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12607,cell12607,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12607 ⟨27,by decide⟩).lower ∧ (cell12607 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12607 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12607 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12607 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12607 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12607 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12607,cell12607,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12607 ⟨28,by decide⟩).lower ∧ (cell12607 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12607 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12607 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12607 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12607 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12607 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12607,cell12607,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12607 ⟨29,by decide⟩).lower ∧ (cell12607 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12607 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12607 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12607 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12607 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12607 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12607,cell12607,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12607 ⟨30,by decide⟩).lower ∧ (cell12607 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12607 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12607 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12607 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12607 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12607 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12607,cell12607,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12607 ⟨31,by decide⟩).lower ∧ (cell12607 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12607 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12607 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12607 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12607 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12607 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12607,cell12607,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12607 ⟨32,by decide⟩).lower ∧ (cell12607 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12607 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12607 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12607 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12607 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12607 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12607,cell12607,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12607 ⟨33,by decide⟩).lower ∧ (cell12607 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12607 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12607 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12607 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12607 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12607 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12607,cell12607,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12607 ⟨34,by decide⟩).lower ∧ (cell12607 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12607 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12607 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12607 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12607 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12607 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12607,cell12607,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12607 ⟨35,by decide⟩).lower ∧ (cell12607 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12607 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12607 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12607 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12607 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12607 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12607,cell12607,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12607 ⟨36,by decide⟩).lower ∧ (cell12607 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12607 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12607 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12607 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12607 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12607 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12607,cell12607,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12607 ⟨37,by decide⟩).lower ∧ (cell12607 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12607 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12607 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12607 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12607 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12607 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12607,cell12607,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12607 ⟨38,by decide⟩).lower ∧ (cell12607 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12607 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12607 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12607 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12607 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12607 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12607,cell12607,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12607 ⟨39,by decide⟩).lower ∧ (cell12607 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12607 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12607 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12607 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12607 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12607 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12607,cell12607,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12607 ⟨40,by decide⟩).lower ∧ (cell12607 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12607 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12607 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12607 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12607 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12607 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12607,cell12607,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12607 ⟨41,by decide⟩).lower ∧ (cell12607 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12607 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12607 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12607 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12607 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12607 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12607,cell12607,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12607 ⟨42,by decide⟩).lower ∧ (cell12607 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12607 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12607 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12607 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12607 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12607 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12607,cell12607,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12607 ⟨43,by decide⟩).lower ∧ (cell12607 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12607 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12607 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12607 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12607 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12607 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12607,cell12607,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12607 ⟨44,by decide⟩).lower ∧ (cell12607 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12607 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12607 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12607 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12607 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12607 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12607,cell12607,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12607 ⟨45,by decide⟩).lower ∧ (cell12607 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12607 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12607 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12607 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12607 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12607 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12607,cell12607,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12607 ⟨46,by decide⟩).lower ∧ (cell12607 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12607 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12607 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12607 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12607 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12607 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12607,cell12607,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12607 ⟨47,by decide⟩).lower ∧ (cell12607 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12607 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12607 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12607 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12607 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12607 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12607,cell12607,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12607 ⟨48,by decide⟩).lower ∧ (cell12607 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12607 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12607 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12607 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12607 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12607 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12607,cell12607,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12607 ⟨49,by decide⟩).lower ∧ (cell12607 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12607 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12607 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12607 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12607 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12607 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12607,cell12607,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12607 ⟨50,by decide⟩).lower ∧ (cell12607 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12607 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12607 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12607 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12607 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12607 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12607,cell12607,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12607 ⟨51,by decide⟩).lower ∧ (cell12607 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12607 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12607 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12607 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12607 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12607 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12607,cell12607,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12607 ⟨52,by decide⟩).lower ∧ (cell12607 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12607 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12607 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12607 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12607 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12607 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12607,cell12607,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12607 i).lower ∧
    (cell12607 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12607 i).upper ≤ (0.532 : ℝ) ∧
    (cell12607 i).centre ≤ (0.1 : ℝ) ∧ (cell12607 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12607 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12607 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12607

/-! The local source numeric instances at 12607 have no network premises. -/
namespace BstLean.Part269.N12607
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12607)
open BstLean.Part268 (cell12607)

noncomputable def sourceNumerics12607 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12607 (cell12607 i)
      scalarRow12607.M scalarRow12607.H scalarRow12607.xi := by
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
    energy_allowance := scalarRow12607.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12607]
    centre_nonneg := (scalarRow12607.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D10.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12607])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12607
/-! Actual 12608 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12608
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12608 ≤ (1.035940783878 : ℝ) := by
  have hr : (112.285350780945 : ℝ) ≤ √(12608 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.285350780945 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12608 12608 (11 / 1000) ≤
    (0.008513016607 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12608) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.285350780945 : ℝ) ≤ √(12608 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12608)
  have hdiv : K / √(12608 : ℝ) ≤ K / 112.285350780945 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.285350780945 ≤ (0.008513016607 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12608.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12608 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12608 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12608 := gPlus_lower 12608
end BstLean.Part269.N12608

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12608
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035940783877 : ℝ) ≤ wn 12608 := by
  have hn : √(12608 : ℝ) ≤ 112.285350780946 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12608 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.285350780946 ≤ 2 / √(12608 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000253751058 : ℝ) ≤ rhoBar 12608 BstLean.Part154.csC ∧
    rhoBar 12608 BstLean.Part154.csC ≤ 0.000253751451 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035940783877 : ℝ) / (1.295212 * 12608) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035940783878 : ℝ) / (1.29521 * 12608) := by gcongr
      _ ≤ (0.000253751451 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12608 BstLean.Part154.csC) ≤ 0.001015070194 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12608 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12608 BstLean.Part154.csC) (piBar (rhoBar 12608 BstLean.Part154.csC)) ≤ 0.000193817137 ∧
    cc1 (rhoBar 12608 BstLean.Part154.csC) (piBar (rhoBar 12608 BstLean.Part154.csC)) ≤ 0.000123327118 ∧
    cc2 (rhoBar 12608 BstLean.Part154.csC) ≤ 0.000071592320 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12608 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12608 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12608 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12608 BstLean.Part154.csC * nuR (rhoBar 12608 BstLean.Part154.csC)) ≤ 0.000507519000 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000253751451 : ℝ) * 0.001015070194 := by gcongr
      _ ≤ (0.000507519000 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12608 BstLean.Part154.csC) * nuR (rhoBar 12608 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001015070194 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12608 BstLean.Part154.csC) * rhoBar 12608 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000253751451 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000253751451 / 2 + 0.399 * 0.001015070194 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000193817137 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000507519000 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123327118 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000253751451 / 1.414213562 := by gcongr
      _ ≤ (0.000071592320 : ℝ) := by norm_num

end BstLean.Part269.N12608

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12608
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12608 BstLean.Part154.csC) (piBar (rhoBar 12608 BstLean.Part154.csC)) ≤ 1.62226E-7 := by
  have hr0 : 0 ≤ rhoBar 12608 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12608 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12608 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12608 BstLean.Part154.csC) (piBar (rhoBar 12608 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12608 BstLean.Part154.csC) (piBar (rhoBar 12608 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12608 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000193817137 : ℝ) ^ 2 + 0.000123327118 ^ 2 + 3 * 0.000071592320 ^ 2 +
        2 * 0.797885 * 0.000193817137 * 0.000123327118 + 2 * 0.000193817137 * 0.000071592320 +
        4 * 0.797885 * 0.000123327118 * 0.000071592320 := by gcongr
    _ ≤ (1.62226E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12608 BstLean.Part154.csC Θ ≤ 0.002649155924 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12608 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12608 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12608 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12608 BstLean.Part154.csC) (piBar (rhoBar 12608 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12608 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035940783878 * 1.62226E-7 / (0.000253751058 : ℝ) := by gcongr
    _ ≤ 0.002649155924 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12608 BstLean.Part154.csC Θ ≤ 0.002939746954 + 0.000669396859 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12608 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12608 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12608 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035940783878 : ℝ) * ((2 * Θ * 0.000253751451 +
        (6863 / 10000) * 0.000253751451 * 12608 * 0.001015070194) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002939746954 + 0.000669396859 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12608 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12608 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12608 0.011 Θ ∧ gammaRatio 12608 0.011 Θ ≤ 0.000087233187 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12608 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035940783878 : ℝ) * 0.525 / ((1 - 0.011) * 12608) := by gcongr
      _ ≤ (0.000087233187 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12608 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12608 0.011 Θ) :=
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
    badAllowance 12608 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000676285396 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12608 BstLean.Part154.csC) 1.22 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 2 (rhoBar 12608 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12608 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12608 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12608 0.011 Θ) 1.12 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 1 (gammaRatio 12608 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12608 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12608 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12608 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12608 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035940783878 : ℝ) * 12608 *
        (2.5110E-8 / 1.1045361 + 3.0670E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000676285396 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12608 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003616032350 + 0.003318552783 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12608

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12608
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12608 BstLean.Part154.csC) (piBar (rhoBar 12608 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12608 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12608 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12608 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12608 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12608 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12608 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12608 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12608 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12608 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12608 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12608 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12608 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12608 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12608 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052677532729 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12608) ≤ 0.010635738080 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12608 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035940783878)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010635738080 + 2 * 0.737676 / 12608) := by gcongr
    _ ≤ (0.052677532729 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12608 12 ≤ 0.0015 := by
  exact BstLean.Part269.S10.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12608

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12608
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560499377419 : ℝ) ≤ plow 12608 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12608) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052864872562)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001390806861) : eMP 12608 0.011 xi bn ≤ 0.001197224822 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12608 : ℝ) * (1 - 0.011))) ≤ 0.000591952865 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001390806861 / (12608 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000591952865 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000591952865 : ℝ) + 3.141593 * 0.052864872562 / (12608 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001197224822 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052864872562)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001390806861) : PiBarMP 12608 12 0.011 xi bn ≤ 0.161844255465 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12608 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037293523044 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.666073630266 : ℝ) ≤ √((12608 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.285350780945 : ℝ) ≤ √(12608 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12608) ≤ 0.124080373494 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037293523044 + 0.052864872562 * 1.772454 / (2 * (111.666073630266 : ℝ))) * (1 + 0.001197224822) +
        8 / (12608 * 112.285350780945) + 0.124080373494 := by gcongr
    _ ≤ (0.161844255465 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052864872562)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001390806861) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282601156053) :
    parallelOracle 12608 0.011 xi bn cd ≤ 0.162842102867 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12608 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12608 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560499377419 : ℝ) ≤ plow 12608 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.285350780945 : ℝ) ≤ √(12608 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282601156053 : ℝ) / (2 * 0.560499377419 * 112.285350780945)) * 0.161844255465 +
        0.282601156053 ^ 2 / (2 * 0.560499377419 * 112.285350780945) := by gcongr
    _ ≤ (0.162842102867 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052864872562) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001390806861)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282601156053) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12608 12608 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560499377419 : ℝ) ≤ plow 12608 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.285350780945 : ℝ) ≤ √(12608 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12608 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12608 Θ 1.22 ≤ 0.011810093577 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.285350780945 := by gcongr <;> linarith
      _ ≤ (0.011810093577 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12608 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12608 12608 0.011 ≤ 0.008513016607 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12608 12608 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12608 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12608 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12608 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12608 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162842102867 + 0.011810093577 + (0.008513016607 : ℝ) *
        (1 + 2 * (0.282601156053 + 0.011810093577) / (0.560499377419 * 112.285350780945))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12608]

end BstLean.Part269.N12608

/-! The original eight local profiles supply actual 12608 moment certificates. -/
namespace BstLean.Part269.N12608
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12608 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12608 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12608 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052864872562 ∧
    0 ≤ bN 12608 BstLean.Part154.csC (groupTheta g) ∧ bN 12608 BstLean.Part154.csC (groupTheta g) ≤ 0.001390806861 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12608 12608 0.011
      (momentAllowance 12608 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12608 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12608 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12608 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12608 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12608 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229923623324 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12608 0.011
      (momentAllowance 12608 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12608 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12608
/-! The actual computed-centre upper energy formula at 12608. -/
namespace BstLean.Part269.N12608
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12608

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12608
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12608)
open BstLean.Part268 (cell12608)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085763289385
  | 2 => 0.086711163887
  | 3 => 0.087657943149
  | 4 => 0.088605220209
  | 5 => 0.089554915934
  | 6 => 0.090509326925
  | 7 => 0.091471177789
  | 8 => 0.092443677786
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12608 12608 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12608 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12608

/-! Actual upper energy certificates on all 43 source endpoints at 12608. -/
namespace BstLean.Part269.N12608
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12608)
open BstLean.Part268 (cell12608)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12608 (gMinus 12608) (1 - (cell12608 i).lower) ≤ 1 ∧
    energyUpper 12608 (gMinus 12608) (BstLean.Part211.gPlus 12608)
      (finiteEnergy 12608 12608 0.011) (1 - (cell12608 i).lower) ≤
      (cell12608 i).energy := by
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
      have E := BstLean.Part269.S10.uniformEnergy10 (n := 12608) (by norm_num)
        (q := 1 - (cell12608 ⟨10,by decide⟩).lower)
        (by norm_num [cell12608]) (by norm_num [cell12608])
      exact ⟨E.1,E.2.trans (by norm_num [cell12608])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy11 (n := 12608) (by norm_num)
        (q := 1 - (cell12608 ⟨11,by decide⟩).lower)
        (by norm_num [cell12608]) (by norm_num [cell12608])
      exact ⟨E.1,E.2.trans (by norm_num [cell12608])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy12 (n := 12608) (by norm_num)
        (q := 1 - (cell12608 ⟨12,by decide⟩).lower)
        (by norm_num [cell12608]) (by norm_num [cell12608])
      exact ⟨E.1,E.2.trans (by norm_num [cell12608])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy13 (n := 12608) (by norm_num)
        (q := 1 - (cell12608 ⟨13,by decide⟩).lower)
        (by norm_num [cell12608]) (by norm_num [cell12608])
      exact ⟨E.1,E.2.trans (by norm_num [cell12608])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy14 (n := 12608) (by norm_num)
        (q := 1 - (cell12608 ⟨14,by decide⟩).lower)
        (by norm_num [cell12608]) (by norm_num [cell12608])
      exact ⟨E.1,E.2.trans (by norm_num [cell12608])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy15 (n := 12608) (by norm_num)
        (q := 1 - (cell12608 ⟨15,by decide⟩).lower)
        (by norm_num [cell12608]) (by norm_num [cell12608])
      exact ⟨E.1,E.2.trans (by norm_num [cell12608])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy16 (n := 12608) (by norm_num)
        (q := 1 - (cell12608 ⟨16,by decide⟩).lower)
        (by norm_num [cell12608]) (by norm_num [cell12608])
      exact ⟨E.1,E.2.trans (by norm_num [cell12608])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy17 (n := 12608) (by norm_num)
        (q := 1 - (cell12608 ⟨17,by decide⟩).lower)
        (by norm_num [cell12608]) (by norm_num [cell12608])
      exact ⟨E.1,E.2.trans (by norm_num [cell12608])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy18 (n := 12608) (by norm_num)
        (q := 1 - (cell12608 ⟨18,by decide⟩).lower)
        (by norm_num [cell12608]) (by norm_num [cell12608])
      exact ⟨E.1,E.2.trans (by norm_num [cell12608])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy19 (n := 12608) (by norm_num)
        (q := 1 - (cell12608 ⟨19,by decide⟩).lower)
        (by norm_num [cell12608]) (by norm_num [cell12608])
      exact ⟨E.1,E.2.trans (by norm_num [cell12608])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy20 (n := 12608) (by norm_num)
        (q := 1 - (cell12608 ⟨20,by decide⟩).lower)
        (by norm_num [cell12608]) (by norm_num [cell12608])
      exact ⟨E.1,E.2.trans (by norm_num [cell12608])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy21 (n := 12608) (by norm_num)
        (q := 1 - (cell12608 ⟨21,by decide⟩).lower)
        (by norm_num [cell12608]) (by norm_num [cell12608])
      exact ⟨E.1,E.2.trans (by norm_num [cell12608])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy22 (n := 12608) (by norm_num)
        (q := 1 - (cell12608 ⟨22,by decide⟩).lower)
        (by norm_num [cell12608]) (by norm_num [cell12608])
      exact ⟨E.1,E.2.trans (by norm_num [cell12608])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy23 (n := 12608) (by norm_num)
        (q := 1 - (cell12608 ⟨23,by decide⟩).lower)
        (by norm_num [cell12608]) (by norm_num [cell12608])
      exact ⟨E.1,E.2.trans (by norm_num [cell12608])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy24 (n := 12608) (by norm_num)
        (q := 1 - (cell12608 ⟨24,by decide⟩).lower)
        (by norm_num [cell12608]) (by norm_num [cell12608])
      exact ⟨E.1,E.2.trans (by norm_num [cell12608])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy25 (n := 12608) (by norm_num)
        (q := 1 - (cell12608 ⟨25,by decide⟩).lower)
        (by norm_num [cell12608]) (by norm_num [cell12608])
      exact ⟨E.1,E.2.trans (by norm_num [cell12608])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy26 (n := 12608) (by norm_num)
        (q := 1 - (cell12608 ⟨26,by decide⟩).lower)
        (by norm_num [cell12608]) (by norm_num [cell12608])
      exact ⟨E.1,E.2.trans (by norm_num [cell12608])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy27 (n := 12608) (by norm_num)
        (q := 1 - (cell12608 ⟨27,by decide⟩).lower)
        (by norm_num [cell12608]) (by norm_num [cell12608])
      exact ⟨E.1,E.2.trans (by norm_num [cell12608])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy28 (n := 12608) (by norm_num)
        (q := 1 - (cell12608 ⟨28,by decide⟩).lower)
        (by norm_num [cell12608]) (by norm_num [cell12608])
      exact ⟨E.1,E.2.trans (by norm_num [cell12608])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy29 (n := 12608) (by norm_num)
        (q := 1 - (cell12608 ⟨29,by decide⟩).lower)
        (by norm_num [cell12608]) (by norm_num [cell12608])
      exact ⟨E.1,E.2.trans (by norm_num [cell12608])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy30 (n := 12608) (by norm_num)
        (q := 1 - (cell12608 ⟨30,by decide⟩).lower)
        (by norm_num [cell12608]) (by norm_num [cell12608])
      exact ⟨E.1,E.2.trans (by norm_num [cell12608])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy31 (n := 12608) (by norm_num)
        (q := 1 - (cell12608 ⟨31,by decide⟩).lower)
        (by norm_num [cell12608]) (by norm_num [cell12608])
      exact ⟨E.1,E.2.trans (by norm_num [cell12608])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy32 (n := 12608) (by norm_num)
        (q := 1 - (cell12608 ⟨32,by decide⟩).lower)
        (by norm_num [cell12608]) (by norm_num [cell12608])
      exact ⟨E.1,E.2.trans (by norm_num [cell12608])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy33 (n := 12608) (by norm_num)
        (q := 1 - (cell12608 ⟨33,by decide⟩).lower)
        (by norm_num [cell12608]) (by norm_num [cell12608])
      exact ⟨E.1,E.2.trans (by norm_num [cell12608])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy34 (n := 12608) (by norm_num)
        (q := 1 - (cell12608 ⟨34,by decide⟩).lower)
        (by norm_num [cell12608]) (by norm_num [cell12608])
      exact ⟨E.1,E.2.trans (by norm_num [cell12608])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy35 (n := 12608) (by norm_num)
        (q := 1 - (cell12608 ⟨35,by decide⟩).lower)
        (by norm_num [cell12608]) (by norm_num [cell12608])
      exact ⟨E.1,E.2.trans (by norm_num [cell12608])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy36 (n := 12608) (by norm_num)
        (q := 1 - (cell12608 ⟨36,by decide⟩).lower)
        (by norm_num [cell12608]) (by norm_num [cell12608])
      exact ⟨E.1,E.2.trans (by norm_num [cell12608])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy37 (n := 12608) (by norm_num)
        (q := 1 - (cell12608 ⟨37,by decide⟩).lower)
        (by norm_num [cell12608]) (by norm_num [cell12608])
      exact ⟨E.1,E.2.trans (by norm_num [cell12608])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy38 (n := 12608) (by norm_num)
        (q := 1 - (cell12608 ⟨38,by decide⟩).lower)
        (by norm_num [cell12608]) (by norm_num [cell12608])
      exact ⟨E.1,E.2.trans (by norm_num [cell12608])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy39 (n := 12608) (by norm_num)
        (q := 1 - (cell12608 ⟨39,by decide⟩).lower)
        (by norm_num [cell12608]) (by norm_num [cell12608])
      exact ⟨E.1,E.2.trans (by norm_num [cell12608])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy40 (n := 12608) (by norm_num)
        (q := 1 - (cell12608 ⟨40,by decide⟩).lower)
        (by norm_num [cell12608]) (by norm_num [cell12608])
      exact ⟨E.1,E.2.trans (by norm_num [cell12608])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy41 (n := 12608) (by norm_num)
        (q := 1 - (cell12608 ⟨41,by decide⟩).lower)
        (by norm_num [cell12608]) (by norm_num [cell12608])
      exact ⟨E.1,E.2.trans (by norm_num [cell12608])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy42 (n := 12608) (by norm_num)
        (q := 1 - (cell12608 ⟨42,by decide⟩).lower)
        (by norm_num [cell12608]) (by norm_num [cell12608])
      exact ⟨E.1,E.2.trans (by norm_num [cell12608])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy43 (n := 12608) (by norm_num)
        (q := 1 - (cell12608 ⟨43,by decide⟩).lower)
        (by norm_num [cell12608]) (by norm_num [cell12608])
      exact ⟨E.1,E.2.trans (by norm_num [cell12608])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy44 (n := 12608) (by norm_num)
        (q := 1 - (cell12608 ⟨44,by decide⟩).lower)
        (by norm_num [cell12608]) (by norm_num [cell12608])
      exact ⟨E.1,E.2.trans (by norm_num [cell12608])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy45 (n := 12608) (by norm_num)
        (q := 1 - (cell12608 ⟨45,by decide⟩).lower)
        (by norm_num [cell12608]) (by norm_num [cell12608])
      exact ⟨E.1,E.2.trans (by norm_num [cell12608])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy46 (n := 12608) (by norm_num)
        (q := 1 - (cell12608 ⟨46,by decide⟩).lower)
        (by norm_num [cell12608]) (by norm_num [cell12608])
      exact ⟨E.1,E.2.trans (by norm_num [cell12608])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy47 (n := 12608) (by norm_num)
        (q := 1 - (cell12608 ⟨47,by decide⟩).lower)
        (by norm_num [cell12608]) (by norm_num [cell12608])
      exact ⟨E.1,E.2.trans (by norm_num [cell12608])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy48 (n := 12608) (by norm_num)
        (q := 1 - (cell12608 ⟨48,by decide⟩).lower)
        (by norm_num [cell12608]) (by norm_num [cell12608])
      exact ⟨E.1,E.2.trans (by norm_num [cell12608])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy49 (n := 12608) (by norm_num)
        (q := 1 - (cell12608 ⟨49,by decide⟩).lower)
        (by norm_num [cell12608]) (by norm_num [cell12608])
      exact ⟨E.1,E.2.trans (by norm_num [cell12608])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy50 (n := 12608) (by norm_num)
        (q := 1 - (cell12608 ⟨50,by decide⟩).lower)
        (by norm_num [cell12608]) (by norm_num [cell12608])
      exact ⟨E.1,E.2.trans (by norm_num [cell12608])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy51 (n := 12608) (by norm_num)
        (q := 1 - (cell12608 ⟨51,by decide⟩).lower)
        (by norm_num [cell12608]) (by norm_num [cell12608])
      exact ⟨E.1,E.2.trans (by norm_num [cell12608])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy52 (n := 12608) (by norm_num)
        (q := 1 - (cell12608 ⟨52,by decide⟩).lower)
        (by norm_num [cell12608]) (by norm_num [cell12608])
      exact ⟨E.1,E.2.trans (by norm_num [cell12608])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12608

/-! Source-cell containment and simple scalar guards at 12608. -/
namespace BstLean.Part269.N12608
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12608)
open BstLean.Part268 (cell12608)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12608 ⟨10,by decide⟩).lower ∧ (cell12608 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12608 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12608 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12608 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12608 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12608 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12608,cell12608,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12608 ⟨11,by decide⟩).lower ∧ (cell12608 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12608 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12608 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12608 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12608 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12608 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12608,cell12608,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12608 ⟨12,by decide⟩).lower ∧ (cell12608 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12608 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12608 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12608 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12608 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12608 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12608,cell12608,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12608 ⟨13,by decide⟩).lower ∧ (cell12608 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12608 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12608 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12608 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12608 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12608 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12608,cell12608,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12608 ⟨14,by decide⟩).lower ∧ (cell12608 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12608 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12608 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12608 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12608 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12608 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12608,cell12608,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12608 ⟨15,by decide⟩).lower ∧ (cell12608 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12608 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12608 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12608 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12608 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12608 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12608,cell12608,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12608 ⟨16,by decide⟩).lower ∧ (cell12608 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12608 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12608 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12608 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12608 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12608 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12608,cell12608,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12608 ⟨17,by decide⟩).lower ∧ (cell12608 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12608 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12608 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12608 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12608 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12608 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12608,cell12608,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12608 ⟨18,by decide⟩).lower ∧ (cell12608 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12608 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12608 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12608 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12608 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12608 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12608,cell12608,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12608 ⟨19,by decide⟩).lower ∧ (cell12608 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12608 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12608 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12608 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12608 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12608 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12608,cell12608,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12608 ⟨20,by decide⟩).lower ∧ (cell12608 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12608 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12608 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12608 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12608 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12608 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12608,cell12608,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12608 ⟨21,by decide⟩).lower ∧ (cell12608 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12608 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12608 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12608 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12608 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12608 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12608,cell12608,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12608 ⟨22,by decide⟩).lower ∧ (cell12608 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12608 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12608 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12608 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12608 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12608 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12608,cell12608,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12608 ⟨23,by decide⟩).lower ∧ (cell12608 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12608 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12608 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12608 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12608 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12608 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12608,cell12608,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12608 ⟨24,by decide⟩).lower ∧ (cell12608 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12608 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12608 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12608 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12608 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12608 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12608,cell12608,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12608 ⟨25,by decide⟩).lower ∧ (cell12608 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12608 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12608 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12608 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12608 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12608 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12608,cell12608,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12608 ⟨26,by decide⟩).lower ∧ (cell12608 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12608 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12608 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12608 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12608 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12608 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12608,cell12608,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12608 ⟨27,by decide⟩).lower ∧ (cell12608 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12608 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12608 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12608 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12608 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12608 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12608,cell12608,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12608 ⟨28,by decide⟩).lower ∧ (cell12608 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12608 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12608 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12608 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12608 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12608 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12608,cell12608,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12608 ⟨29,by decide⟩).lower ∧ (cell12608 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12608 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12608 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12608 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12608 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12608 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12608,cell12608,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12608 ⟨30,by decide⟩).lower ∧ (cell12608 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12608 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12608 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12608 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12608 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12608 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12608,cell12608,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12608 ⟨31,by decide⟩).lower ∧ (cell12608 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12608 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12608 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12608 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12608 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12608 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12608,cell12608,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12608 ⟨32,by decide⟩).lower ∧ (cell12608 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12608 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12608 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12608 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12608 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12608 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12608,cell12608,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12608 ⟨33,by decide⟩).lower ∧ (cell12608 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12608 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12608 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12608 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12608 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12608 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12608,cell12608,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12608 ⟨34,by decide⟩).lower ∧ (cell12608 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12608 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12608 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12608 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12608 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12608 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12608,cell12608,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12608 ⟨35,by decide⟩).lower ∧ (cell12608 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12608 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12608 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12608 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12608 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12608 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12608,cell12608,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12608 ⟨36,by decide⟩).lower ∧ (cell12608 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12608 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12608 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12608 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12608 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12608 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12608,cell12608,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12608 ⟨37,by decide⟩).lower ∧ (cell12608 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12608 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12608 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12608 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12608 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12608 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12608,cell12608,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12608 ⟨38,by decide⟩).lower ∧ (cell12608 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12608 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12608 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12608 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12608 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12608 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12608,cell12608,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12608 ⟨39,by decide⟩).lower ∧ (cell12608 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12608 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12608 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12608 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12608 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12608 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12608,cell12608,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12608 ⟨40,by decide⟩).lower ∧ (cell12608 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12608 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12608 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12608 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12608 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12608 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12608,cell12608,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12608 ⟨41,by decide⟩).lower ∧ (cell12608 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12608 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12608 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12608 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12608 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12608 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12608,cell12608,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12608 ⟨42,by decide⟩).lower ∧ (cell12608 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12608 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12608 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12608 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12608 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12608 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12608,cell12608,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12608 ⟨43,by decide⟩).lower ∧ (cell12608 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12608 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12608 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12608 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12608 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12608 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12608,cell12608,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12608 ⟨44,by decide⟩).lower ∧ (cell12608 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12608 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12608 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12608 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12608 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12608 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12608,cell12608,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12608 ⟨45,by decide⟩).lower ∧ (cell12608 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12608 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12608 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12608 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12608 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12608 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12608,cell12608,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12608 ⟨46,by decide⟩).lower ∧ (cell12608 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12608 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12608 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12608 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12608 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12608 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12608,cell12608,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12608 ⟨47,by decide⟩).lower ∧ (cell12608 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12608 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12608 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12608 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12608 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12608 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12608,cell12608,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12608 ⟨48,by decide⟩).lower ∧ (cell12608 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12608 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12608 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12608 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12608 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12608 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12608,cell12608,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12608 ⟨49,by decide⟩).lower ∧ (cell12608 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12608 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12608 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12608 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12608 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12608 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12608,cell12608,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12608 ⟨50,by decide⟩).lower ∧ (cell12608 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12608 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12608 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12608 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12608 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12608 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12608,cell12608,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12608 ⟨51,by decide⟩).lower ∧ (cell12608 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12608 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12608 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12608 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12608 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12608 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12608,cell12608,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12608 ⟨52,by decide⟩).lower ∧ (cell12608 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12608 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12608 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12608 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12608 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12608 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12608,cell12608,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12608 i).lower ∧
    (cell12608 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12608 i).upper ≤ (0.532 : ℝ) ∧
    (cell12608 i).centre ≤ (0.1 : ℝ) ∧ (cell12608 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12608 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12608 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12608

/-! The local source numeric instances at 12608 have no network premises. -/
namespace BstLean.Part269.N12608
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12608)
open BstLean.Part268 (cell12608)

noncomputable def sourceNumerics12608 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12608 (cell12608 i)
      scalarRow12608.M scalarRow12608.H scalarRow12608.xi := by
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
    energy_allowance := scalarRow12608.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12608]
    centre_nonneg := (scalarRow12608.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D10.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12608])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12608
/-! Actual 12609 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12609
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12609 ≤ (1.035939346065 : ℝ) := by
  have hr : (112.289803633277 : ℝ) ≤ √(12609 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.289803633277 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12609 12609 (11 / 1000) ≤
    (0.008512679021 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12609) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.289803633277 : ℝ) ≤ √(12609 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12609)
  have hdiv : K / √(12609 : ℝ) ≤ K / 112.289803633277 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.289803633277 ≤ (0.008512679021 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12609.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12609 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12609 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12609 := gPlus_lower 12609
end BstLean.Part269.N12609

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12609
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035939346064 : ℝ) ≤ wn 12609 := by
  have hn : √(12609 : ℝ) ≤ 112.289803633278 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12609 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.289803633278 ≤ 2 / √(12609 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000253730581 : ℝ) ≤ rhoBar 12609 BstLean.Part154.csC ∧
    rhoBar 12609 BstLean.Part154.csC ≤ 0.000253730974 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035939346064 : ℝ) / (1.295212 * 12609) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035939346065 : ℝ) / (1.29521 * 12609) := by gcongr
      _ ≤ (0.000253730974 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12609 BstLean.Part154.csC) ≤ 0.001014988276 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12609 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12609 BstLean.Part154.csC) (piBar (rhoBar 12609 BstLean.Part154.csC)) ≤ 0.000193801496 ∧
    cc1 (rhoBar 12609 BstLean.Part154.csC) (piBar (rhoBar 12609 BstLean.Part154.csC)) ≤ 0.000123317165 ∧
    cc2 (rhoBar 12609 BstLean.Part154.csC) ≤ 0.000071586543 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12609 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12609 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12609 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12609 BstLean.Part154.csC * nuR (rhoBar 12609 BstLean.Part154.csC)) ≤ 0.000507478043 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000253730974 : ℝ) * 0.001014988276 := by gcongr
      _ ≤ (0.000507478043 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12609 BstLean.Part154.csC) * nuR (rhoBar 12609 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001014988276 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12609 BstLean.Part154.csC) * rhoBar 12609 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000253730974 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000253730974 / 2 + 0.399 * 0.001014988276 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000193801496 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000507478043 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123317165 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000253730974 / 1.414213562 := by gcongr
      _ ≤ (0.000071586543 : ℝ) := by norm_num

end BstLean.Part269.N12609

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12609
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12609 BstLean.Part154.csC) (piBar (rhoBar 12609 BstLean.Part154.csC)) ≤ 1.62200E-7 := by
  have hr0 : 0 ≤ rhoBar 12609 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12609 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12609 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12609 BstLean.Part154.csC) (piBar (rhoBar 12609 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12609 BstLean.Part154.csC) (piBar (rhoBar 12609 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12609 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000193801496 : ℝ) ^ 2 + 0.000123317165 ^ 2 + 3 * 0.000071586543 ^ 2 +
        2 * 0.797885 * 0.000193801496 * 0.000123317165 + 2 * 0.000193801496 * 0.000071586543 +
        4 * 0.797885 * 0.000123317165 * 0.000071586543 := by gcongr
    _ ≤ (1.62200E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12609 BstLean.Part154.csC Θ ≤ 0.002648941429 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12609 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12609 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12609 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12609 BstLean.Part154.csC) (piBar (rhoBar 12609 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12609 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035939346065 * 1.62200E-7 / (0.000253730581 : ℝ) := by gcongr
    _ ≤ 0.002648941429 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12609 BstLean.Part154.csC Θ ≤ 0.002939501549 + 0.000669341912 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12609 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12609 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12609 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035939346065 : ℝ) * ((2 * Θ * 0.000253730974 +
        (6863 / 10000) * 0.000253730974 * 12609 * 0.001014988276) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002939501549 + 0.000669341912 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12609 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12609 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12609 0.011 Θ ∧ gammaRatio 12609 0.011 Θ ≤ 0.000087226148 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12609 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035939346065 : ℝ) * 0.525 / ((1 - 0.011) * 12609) := by gcongr
      _ ≤ (0.000087226148 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12609 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12609 0.011 Θ) :=
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
    badAllowance 12609 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000676285396 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12609 BstLean.Part154.csC) 1.22 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 2 (rhoBar 12609 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12609 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12609 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12609 0.011 Θ) 1.12 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 1 (gammaRatio 12609 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12609 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12609 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12609 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12609 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035939346065 : ℝ) * 12609 *
        (2.5110E-8 / 1.1045361 + 3.0670E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000676285396 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12609 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003615786945 + 0.003318283341 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12609

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12609
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12609 BstLean.Part154.csC) (piBar (rhoBar 12609 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12609 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12609 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12609 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12609 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12609 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12609 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12609 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12609 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12609 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12609 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12609 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12609 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12609 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12609 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052675421070 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12609) ≤ 0.010635316320 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12609 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035939346065)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010635316320 + 2 * 0.737676 / 12609) := by gcongr
    _ ≤ (0.052675421070 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12609 12 ≤ 0.0015 := by
  exact BstLean.Part269.S10.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12609

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12609
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560499423300 : ℝ) ≤ plow 12609 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12609) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052864485700)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001390694251) : eMP 12609 0.011 xi bn ≤ 0.001197128793 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12609 : ℝ) * (1 - 0.011))) ≤ 0.000591905427 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001390694251 / (12609 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000591905427 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000591905427 : ℝ) + 3.141593 * 0.052864485700 / (12609 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001197128793 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052864485700)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001390694251) : PiBarMP 12609 12 0.011 xi bn ≤ 0.161837799416 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12609 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037292013234 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.670501924187 : ℝ) ≤ √((12609 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.289803633277 : ℝ) ≤ √(12609 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12609) ≤ 0.124075453087 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037292013234 + 0.052864485700 * 1.772454 / (2 * (111.670501924187 : ℝ))) * (1 + 0.001197128793) +
        8 / (12609 * 112.289803633277) + 0.124075453087 := by gcongr
    _ ≤ (0.161837799416 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052864485700)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001390694251) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282598203108) :
    parallelOracle 12609 0.011 xi bn cd ≤ 0.162835575617 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12609 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12609 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560499423300 : ℝ) ≤ plow 12609 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.289803633277 : ℝ) ≤ √(12609 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282598203108 : ℝ) / (2 * 0.560499423300 * 112.289803633277)) * 0.161837799416 +
        0.282598203108 ^ 2 / (2 * 0.560499423300 * 112.289803633277) := by gcongr
    _ ≤ (0.162835575617 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052864485700) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001390694251)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282598203108) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12609 12609 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560499423300 : ℝ) ≤ plow 12609 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.289803633277 : ℝ) ≤ √(12609 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12609 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12609 Θ 1.22 ≤ 0.011809625248 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.289803633277 := by gcongr <;> linarith
      _ ≤ (0.011809625248 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12609 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12609 12609 0.011 ≤ 0.008512679021 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12609 12609 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12609 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12609 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12609 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12609 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162835575617 + 0.011809625248 + (0.008512679021 : ℝ) *
        (1 + 2 * (0.282598203108 + 0.011809625248) / (0.560499423300 * 112.289803633277))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12609]

end BstLean.Part269.N12609

/-! The original eight local profiles supply actual 12609 moment certificates. -/
namespace BstLean.Part269.N12609
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12609 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12609 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12609 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052864485700 ∧
    0 ≤ bN 12609 BstLean.Part154.csC (groupTheta g) ∧ bN 12609 BstLean.Part154.csC (groupTheta g) ≤ 0.001390694251 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12609 12609 0.011
      (momentAllowance 12609 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12609 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12609 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12609 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12609 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12609 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229922782038 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12609 0.011
      (momentAllowance 12609 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12609 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12609
/-! The actual computed-centre upper energy formula at 12609. -/
namespace BstLean.Part269.N12609
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12609

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12609
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12609)
open BstLean.Part268 (cell12609)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085760269127
  | 2 => 0.086708085728
  | 3 => 0.087654798257
  | 4 => 0.088601997748
  | 5 => 0.089551602712
  | 6 => 0.090505907003
  | 7 => 0.091467632047
  | 8 => 0.092439983439
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12609 12609 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12609 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12609

/-! Actual upper energy certificates on all 43 source endpoints at 12609. -/
namespace BstLean.Part269.N12609
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12609)
open BstLean.Part268 (cell12609)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12609 (gMinus 12609) (1 - (cell12609 i).lower) ≤ 1 ∧
    energyUpper 12609 (gMinus 12609) (BstLean.Part211.gPlus 12609)
      (finiteEnergy 12609 12609 0.011) (1 - (cell12609 i).lower) ≤
      (cell12609 i).energy := by
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
      have E := BstLean.Part269.S10.uniformEnergy10 (n := 12609) (by norm_num)
        (q := 1 - (cell12609 ⟨10,by decide⟩).lower)
        (by norm_num [cell12609]) (by norm_num [cell12609])
      exact ⟨E.1,E.2.trans (by norm_num [cell12609])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy11 (n := 12609) (by norm_num)
        (q := 1 - (cell12609 ⟨11,by decide⟩).lower)
        (by norm_num [cell12609]) (by norm_num [cell12609])
      exact ⟨E.1,E.2.trans (by norm_num [cell12609])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy12 (n := 12609) (by norm_num)
        (q := 1 - (cell12609 ⟨12,by decide⟩).lower)
        (by norm_num [cell12609]) (by norm_num [cell12609])
      exact ⟨E.1,E.2.trans (by norm_num [cell12609])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy13 (n := 12609) (by norm_num)
        (q := 1 - (cell12609 ⟨13,by decide⟩).lower)
        (by norm_num [cell12609]) (by norm_num [cell12609])
      exact ⟨E.1,E.2.trans (by norm_num [cell12609])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy14 (n := 12609) (by norm_num)
        (q := 1 - (cell12609 ⟨14,by decide⟩).lower)
        (by norm_num [cell12609]) (by norm_num [cell12609])
      exact ⟨E.1,E.2.trans (by norm_num [cell12609])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy15 (n := 12609) (by norm_num)
        (q := 1 - (cell12609 ⟨15,by decide⟩).lower)
        (by norm_num [cell12609]) (by norm_num [cell12609])
      exact ⟨E.1,E.2.trans (by norm_num [cell12609])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy16 (n := 12609) (by norm_num)
        (q := 1 - (cell12609 ⟨16,by decide⟩).lower)
        (by norm_num [cell12609]) (by norm_num [cell12609])
      exact ⟨E.1,E.2.trans (by norm_num [cell12609])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy17 (n := 12609) (by norm_num)
        (q := 1 - (cell12609 ⟨17,by decide⟩).lower)
        (by norm_num [cell12609]) (by norm_num [cell12609])
      exact ⟨E.1,E.2.trans (by norm_num [cell12609])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy18 (n := 12609) (by norm_num)
        (q := 1 - (cell12609 ⟨18,by decide⟩).lower)
        (by norm_num [cell12609]) (by norm_num [cell12609])
      exact ⟨E.1,E.2.trans (by norm_num [cell12609])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy19 (n := 12609) (by norm_num)
        (q := 1 - (cell12609 ⟨19,by decide⟩).lower)
        (by norm_num [cell12609]) (by norm_num [cell12609])
      exact ⟨E.1,E.2.trans (by norm_num [cell12609])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy20 (n := 12609) (by norm_num)
        (q := 1 - (cell12609 ⟨20,by decide⟩).lower)
        (by norm_num [cell12609]) (by norm_num [cell12609])
      exact ⟨E.1,E.2.trans (by norm_num [cell12609])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy21 (n := 12609) (by norm_num)
        (q := 1 - (cell12609 ⟨21,by decide⟩).lower)
        (by norm_num [cell12609]) (by norm_num [cell12609])
      exact ⟨E.1,E.2.trans (by norm_num [cell12609])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy22 (n := 12609) (by norm_num)
        (q := 1 - (cell12609 ⟨22,by decide⟩).lower)
        (by norm_num [cell12609]) (by norm_num [cell12609])
      exact ⟨E.1,E.2.trans (by norm_num [cell12609])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy23 (n := 12609) (by norm_num)
        (q := 1 - (cell12609 ⟨23,by decide⟩).lower)
        (by norm_num [cell12609]) (by norm_num [cell12609])
      exact ⟨E.1,E.2.trans (by norm_num [cell12609])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy24 (n := 12609) (by norm_num)
        (q := 1 - (cell12609 ⟨24,by decide⟩).lower)
        (by norm_num [cell12609]) (by norm_num [cell12609])
      exact ⟨E.1,E.2.trans (by norm_num [cell12609])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy25 (n := 12609) (by norm_num)
        (q := 1 - (cell12609 ⟨25,by decide⟩).lower)
        (by norm_num [cell12609]) (by norm_num [cell12609])
      exact ⟨E.1,E.2.trans (by norm_num [cell12609])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy26 (n := 12609) (by norm_num)
        (q := 1 - (cell12609 ⟨26,by decide⟩).lower)
        (by norm_num [cell12609]) (by norm_num [cell12609])
      exact ⟨E.1,E.2.trans (by norm_num [cell12609])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy27 (n := 12609) (by norm_num)
        (q := 1 - (cell12609 ⟨27,by decide⟩).lower)
        (by norm_num [cell12609]) (by norm_num [cell12609])
      exact ⟨E.1,E.2.trans (by norm_num [cell12609])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy28 (n := 12609) (by norm_num)
        (q := 1 - (cell12609 ⟨28,by decide⟩).lower)
        (by norm_num [cell12609]) (by norm_num [cell12609])
      exact ⟨E.1,E.2.trans (by norm_num [cell12609])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy29 (n := 12609) (by norm_num)
        (q := 1 - (cell12609 ⟨29,by decide⟩).lower)
        (by norm_num [cell12609]) (by norm_num [cell12609])
      exact ⟨E.1,E.2.trans (by norm_num [cell12609])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy30 (n := 12609) (by norm_num)
        (q := 1 - (cell12609 ⟨30,by decide⟩).lower)
        (by norm_num [cell12609]) (by norm_num [cell12609])
      exact ⟨E.1,E.2.trans (by norm_num [cell12609])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy31 (n := 12609) (by norm_num)
        (q := 1 - (cell12609 ⟨31,by decide⟩).lower)
        (by norm_num [cell12609]) (by norm_num [cell12609])
      exact ⟨E.1,E.2.trans (by norm_num [cell12609])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy32 (n := 12609) (by norm_num)
        (q := 1 - (cell12609 ⟨32,by decide⟩).lower)
        (by norm_num [cell12609]) (by norm_num [cell12609])
      exact ⟨E.1,E.2.trans (by norm_num [cell12609])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy33 (n := 12609) (by norm_num)
        (q := 1 - (cell12609 ⟨33,by decide⟩).lower)
        (by norm_num [cell12609]) (by norm_num [cell12609])
      exact ⟨E.1,E.2.trans (by norm_num [cell12609])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy34 (n := 12609) (by norm_num)
        (q := 1 - (cell12609 ⟨34,by decide⟩).lower)
        (by norm_num [cell12609]) (by norm_num [cell12609])
      exact ⟨E.1,E.2.trans (by norm_num [cell12609])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy35 (n := 12609) (by norm_num)
        (q := 1 - (cell12609 ⟨35,by decide⟩).lower)
        (by norm_num [cell12609]) (by norm_num [cell12609])
      exact ⟨E.1,E.2.trans (by norm_num [cell12609])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy36 (n := 12609) (by norm_num)
        (q := 1 - (cell12609 ⟨36,by decide⟩).lower)
        (by norm_num [cell12609]) (by norm_num [cell12609])
      exact ⟨E.1,E.2.trans (by norm_num [cell12609])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy37 (n := 12609) (by norm_num)
        (q := 1 - (cell12609 ⟨37,by decide⟩).lower)
        (by norm_num [cell12609]) (by norm_num [cell12609])
      exact ⟨E.1,E.2.trans (by norm_num [cell12609])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy38 (n := 12609) (by norm_num)
        (q := 1 - (cell12609 ⟨38,by decide⟩).lower)
        (by norm_num [cell12609]) (by norm_num [cell12609])
      exact ⟨E.1,E.2.trans (by norm_num [cell12609])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy39 (n := 12609) (by norm_num)
        (q := 1 - (cell12609 ⟨39,by decide⟩).lower)
        (by norm_num [cell12609]) (by norm_num [cell12609])
      exact ⟨E.1,E.2.trans (by norm_num [cell12609])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy40 (n := 12609) (by norm_num)
        (q := 1 - (cell12609 ⟨40,by decide⟩).lower)
        (by norm_num [cell12609]) (by norm_num [cell12609])
      exact ⟨E.1,E.2.trans (by norm_num [cell12609])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy41 (n := 12609) (by norm_num)
        (q := 1 - (cell12609 ⟨41,by decide⟩).lower)
        (by norm_num [cell12609]) (by norm_num [cell12609])
      exact ⟨E.1,E.2.trans (by norm_num [cell12609])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy42 (n := 12609) (by norm_num)
        (q := 1 - (cell12609 ⟨42,by decide⟩).lower)
        (by norm_num [cell12609]) (by norm_num [cell12609])
      exact ⟨E.1,E.2.trans (by norm_num [cell12609])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy43 (n := 12609) (by norm_num)
        (q := 1 - (cell12609 ⟨43,by decide⟩).lower)
        (by norm_num [cell12609]) (by norm_num [cell12609])
      exact ⟨E.1,E.2.trans (by norm_num [cell12609])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy44 (n := 12609) (by norm_num)
        (q := 1 - (cell12609 ⟨44,by decide⟩).lower)
        (by norm_num [cell12609]) (by norm_num [cell12609])
      exact ⟨E.1,E.2.trans (by norm_num [cell12609])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy45 (n := 12609) (by norm_num)
        (q := 1 - (cell12609 ⟨45,by decide⟩).lower)
        (by norm_num [cell12609]) (by norm_num [cell12609])
      exact ⟨E.1,E.2.trans (by norm_num [cell12609])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy46 (n := 12609) (by norm_num)
        (q := 1 - (cell12609 ⟨46,by decide⟩).lower)
        (by norm_num [cell12609]) (by norm_num [cell12609])
      exact ⟨E.1,E.2.trans (by norm_num [cell12609])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy47 (n := 12609) (by norm_num)
        (q := 1 - (cell12609 ⟨47,by decide⟩).lower)
        (by norm_num [cell12609]) (by norm_num [cell12609])
      exact ⟨E.1,E.2.trans (by norm_num [cell12609])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy48 (n := 12609) (by norm_num)
        (q := 1 - (cell12609 ⟨48,by decide⟩).lower)
        (by norm_num [cell12609]) (by norm_num [cell12609])
      exact ⟨E.1,E.2.trans (by norm_num [cell12609])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy49 (n := 12609) (by norm_num)
        (q := 1 - (cell12609 ⟨49,by decide⟩).lower)
        (by norm_num [cell12609]) (by norm_num [cell12609])
      exact ⟨E.1,E.2.trans (by norm_num [cell12609])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy50 (n := 12609) (by norm_num)
        (q := 1 - (cell12609 ⟨50,by decide⟩).lower)
        (by norm_num [cell12609]) (by norm_num [cell12609])
      exact ⟨E.1,E.2.trans (by norm_num [cell12609])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy51 (n := 12609) (by norm_num)
        (q := 1 - (cell12609 ⟨51,by decide⟩).lower)
        (by norm_num [cell12609]) (by norm_num [cell12609])
      exact ⟨E.1,E.2.trans (by norm_num [cell12609])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy52 (n := 12609) (by norm_num)
        (q := 1 - (cell12609 ⟨52,by decide⟩).lower)
        (by norm_num [cell12609]) (by norm_num [cell12609])
      exact ⟨E.1,E.2.trans (by norm_num [cell12609])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12609

/-! Source-cell containment and simple scalar guards at 12609. -/
namespace BstLean.Part269.N12609
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12609)
open BstLean.Part268 (cell12609)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12609 ⟨10,by decide⟩).lower ∧ (cell12609 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12609 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12609 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12609 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12609 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12609 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12609,cell12609,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12609 ⟨11,by decide⟩).lower ∧ (cell12609 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12609 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12609 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12609 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12609 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12609 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12609,cell12609,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12609 ⟨12,by decide⟩).lower ∧ (cell12609 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12609 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12609 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12609 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12609 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12609 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12609,cell12609,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12609 ⟨13,by decide⟩).lower ∧ (cell12609 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12609 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12609 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12609 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12609 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12609 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12609,cell12609,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12609 ⟨14,by decide⟩).lower ∧ (cell12609 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12609 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12609 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12609 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12609 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12609 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12609,cell12609,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12609 ⟨15,by decide⟩).lower ∧ (cell12609 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12609 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12609 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12609 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12609 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12609 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12609,cell12609,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12609 ⟨16,by decide⟩).lower ∧ (cell12609 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12609 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12609 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12609 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12609 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12609 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12609,cell12609,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12609 ⟨17,by decide⟩).lower ∧ (cell12609 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12609 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12609 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12609 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12609 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12609 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12609,cell12609,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12609 ⟨18,by decide⟩).lower ∧ (cell12609 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12609 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12609 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12609 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12609 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12609 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12609,cell12609,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12609 ⟨19,by decide⟩).lower ∧ (cell12609 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12609 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12609 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12609 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12609 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12609 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12609,cell12609,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12609 ⟨20,by decide⟩).lower ∧ (cell12609 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12609 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12609 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12609 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12609 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12609 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12609,cell12609,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12609 ⟨21,by decide⟩).lower ∧ (cell12609 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12609 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12609 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12609 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12609 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12609 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12609,cell12609,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12609 ⟨22,by decide⟩).lower ∧ (cell12609 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12609 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12609 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12609 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12609 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12609 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12609,cell12609,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12609 ⟨23,by decide⟩).lower ∧ (cell12609 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12609 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12609 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12609 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12609 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12609 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12609,cell12609,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12609 ⟨24,by decide⟩).lower ∧ (cell12609 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12609 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12609 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12609 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12609 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12609 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12609,cell12609,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12609 ⟨25,by decide⟩).lower ∧ (cell12609 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12609 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12609 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12609 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12609 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12609 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12609,cell12609,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12609 ⟨26,by decide⟩).lower ∧ (cell12609 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12609 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12609 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12609 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12609 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12609 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12609,cell12609,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12609 ⟨27,by decide⟩).lower ∧ (cell12609 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12609 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12609 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12609 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12609 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12609 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12609,cell12609,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12609 ⟨28,by decide⟩).lower ∧ (cell12609 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12609 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12609 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12609 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12609 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12609 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12609,cell12609,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12609 ⟨29,by decide⟩).lower ∧ (cell12609 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12609 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12609 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12609 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12609 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12609 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12609,cell12609,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12609 ⟨30,by decide⟩).lower ∧ (cell12609 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12609 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12609 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12609 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12609 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12609 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12609,cell12609,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12609 ⟨31,by decide⟩).lower ∧ (cell12609 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12609 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12609 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12609 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12609 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12609 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12609,cell12609,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12609 ⟨32,by decide⟩).lower ∧ (cell12609 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12609 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12609 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12609 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12609 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12609 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12609,cell12609,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12609 ⟨33,by decide⟩).lower ∧ (cell12609 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12609 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12609 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12609 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12609 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12609 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12609,cell12609,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12609 ⟨34,by decide⟩).lower ∧ (cell12609 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12609 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12609 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12609 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12609 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12609 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12609,cell12609,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12609 ⟨35,by decide⟩).lower ∧ (cell12609 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12609 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12609 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12609 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12609 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12609 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12609,cell12609,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12609 ⟨36,by decide⟩).lower ∧ (cell12609 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12609 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12609 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12609 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12609 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12609 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12609,cell12609,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12609 ⟨37,by decide⟩).lower ∧ (cell12609 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12609 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12609 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12609 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12609 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12609 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12609,cell12609,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12609 ⟨38,by decide⟩).lower ∧ (cell12609 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12609 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12609 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12609 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12609 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12609 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12609,cell12609,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12609 ⟨39,by decide⟩).lower ∧ (cell12609 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12609 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12609 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12609 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12609 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12609 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12609,cell12609,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12609 ⟨40,by decide⟩).lower ∧ (cell12609 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12609 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12609 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12609 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12609 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12609 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12609,cell12609,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12609 ⟨41,by decide⟩).lower ∧ (cell12609 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12609 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12609 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12609 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12609 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12609 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12609,cell12609,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12609 ⟨42,by decide⟩).lower ∧ (cell12609 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12609 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12609 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12609 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12609 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12609 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12609,cell12609,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12609 ⟨43,by decide⟩).lower ∧ (cell12609 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12609 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12609 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12609 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12609 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12609 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12609,cell12609,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12609 ⟨44,by decide⟩).lower ∧ (cell12609 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12609 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12609 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12609 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12609 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12609 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12609,cell12609,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12609 ⟨45,by decide⟩).lower ∧ (cell12609 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12609 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12609 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12609 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12609 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12609 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12609,cell12609,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12609 ⟨46,by decide⟩).lower ∧ (cell12609 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12609 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12609 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12609 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12609 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12609 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12609,cell12609,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12609 ⟨47,by decide⟩).lower ∧ (cell12609 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12609 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12609 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12609 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12609 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12609 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12609,cell12609,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12609 ⟨48,by decide⟩).lower ∧ (cell12609 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12609 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12609 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12609 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12609 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12609 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12609,cell12609,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12609 ⟨49,by decide⟩).lower ∧ (cell12609 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12609 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12609 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12609 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12609 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12609 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12609,cell12609,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12609 ⟨50,by decide⟩).lower ∧ (cell12609 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12609 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12609 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12609 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12609 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12609 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12609,cell12609,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12609 ⟨51,by decide⟩).lower ∧ (cell12609 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12609 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12609 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12609 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12609 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12609 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12609,cell12609,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12609 ⟨52,by decide⟩).lower ∧ (cell12609 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12609 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12609 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12609 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12609 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12609 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12609,cell12609,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12609 i).lower ∧
    (cell12609 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12609 i).upper ≤ (0.532 : ℝ) ∧
    (cell12609 i).centre ≤ (0.1 : ℝ) ∧ (cell12609 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12609 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12609 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12609

/-! The local source numeric instances at 12609 have no network premises. -/
namespace BstLean.Part269.N12609
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12609)
open BstLean.Part268 (cell12609)

noncomputable def sourceNumerics12609 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12609 (cell12609 i)
      scalarRow12609.M scalarRow12609.H scalarRow12609.xi := by
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
    energy_allowance := scalarRow12609.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12609]
    centre_nonneg := (scalarRow12609.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D10.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12609])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12609
/-! Actual 12610 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12610
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12610 ≤ (1.035937908425 : ℝ) := by
  have hr : (112.294256309038 : ℝ) ≤ √(12610 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.294256309038 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12610 12610 (11 / 1000) ≤
    (0.008512341475 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12610) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.294256309038 : ℝ) ≤ √(12610 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12610)
  have hdiv : K / √(12610 : ℝ) ≤ K / 112.294256309038 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.294256309038 ≤ (0.008512341475 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12610.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12610 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12610 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12610 := gPlus_lower 12610
end BstLean.Part269.N12610

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12610
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035937908424 : ℝ) ≤ wn 12610 := by
  have hn : √(12610 : ℝ) ≤ 112.294256309039 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12610 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.294256309039 ≤ 2 / √(12610 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000253710108 : ℝ) ≤ rhoBar 12610 BstLean.Part154.csC ∧
    rhoBar 12610 BstLean.Part154.csC ≤ 0.000253710501 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035937908424 : ℝ) / (1.295212 * 12610) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035937908425 : ℝ) / (1.29521 * 12610) := by gcongr
      _ ≤ (0.000253710501 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12610 BstLean.Part154.csC) ≤ 0.001014906374 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12610 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12610 BstLean.Part154.csC) (piBar (rhoBar 12610 BstLean.Part154.csC)) ≤ 0.000193785858 ∧
    cc1 (rhoBar 12610 BstLean.Part154.csC) (piBar (rhoBar 12610 BstLean.Part154.csC)) ≤ 0.000123307215 ∧
    cc2 (rhoBar 12610 BstLean.Part154.csC) ≤ 0.000071580766 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12610 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12610 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12610 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12610 BstLean.Part154.csC * nuR (rhoBar 12610 BstLean.Part154.csC)) ≤ 0.000507437095 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000253710501 : ℝ) * 0.001014906374 := by gcongr
      _ ≤ (0.000507437095 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12610 BstLean.Part154.csC) * nuR (rhoBar 12610 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001014906374 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12610 BstLean.Part154.csC) * rhoBar 12610 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000253710501 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000253710501 / 2 + 0.399 * 0.001014906374 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000193785858 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000507437095 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123307215 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000253710501 / 1.414213562 := by gcongr
      _ ≤ (0.000071580766 : ℝ) := by norm_num

end BstLean.Part269.N12610

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12610
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12610 BstLean.Part154.csC) (piBar (rhoBar 12610 BstLean.Part154.csC)) ≤ 1.62173E-7 := by
  have hr0 : 0 ≤ rhoBar 12610 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12610 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12610 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12610 BstLean.Part154.csC) (piBar (rhoBar 12610 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12610 BstLean.Part154.csC) (piBar (rhoBar 12610 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12610 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000193785858 : ℝ) ^ 2 + 0.000123307215 ^ 2 + 3 * 0.000071580766 ^ 2 +
        2 * 0.797885 * 0.000193785858 * 0.000123307215 + 2 * 0.000193785858 * 0.000071580766 +
        4 * 0.797885 * 0.000123307215 * 0.000071580766 := by gcongr
    _ ≤ (1.62173E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12610 BstLean.Part154.csC Θ ≤ 0.002648710527 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12610 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12610 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12610 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12610 BstLean.Part154.csC) (piBar (rhoBar 12610 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12610 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035937908425 * 1.62173E-7 / (0.000253710108 : ℝ) := by gcongr
    _ ≤ 0.002648710527 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12610 BstLean.Part154.csC Θ ≤ 0.002939256201 + 0.000669286975 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12610 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12610 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12610 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035937908425 : ℝ) * ((2 * Θ * 0.000253710501 +
        (6863 / 10000) * 0.000253710501 * 12610 * 0.001014906374) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002939256201 + 0.000669286975 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12610 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12610 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12610 0.011 Θ ∧ gammaRatio 12610 0.011 Θ ≤ 0.000087219110 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12610 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035937908425 : ℝ) * 0.525 / ((1 - 0.011) * 12610) := by gcongr
      _ ≤ (0.000087219110 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12610 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12610 0.011 Θ) :=
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
    badAllowance 12610 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000676285396 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12610 BstLean.Part154.csC) 1.22 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 2 (rhoBar 12610 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12610 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12610 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12610 0.011 Θ) 1.12 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 1 (gammaRatio 12610 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12610 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12610 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12610 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12610 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035937908425 : ℝ) * 12610 *
        (2.5110E-8 / 1.1045361 + 3.0670E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000676285396 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12610 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003615541597 + 0.003317997502 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12610

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12610
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12610 BstLean.Part154.csC) (piBar (rhoBar 12610 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12610 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12610 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12610 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12610 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12610 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12610 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12610 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12610 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12610 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12610 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12610 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12610 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12610 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12610 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052673309664 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12610) ≤ 0.010634894610 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12610 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035937908425)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010634894610 + 2 * 0.737676 / 12610) := by gcongr
    _ ≤ (0.052673309664 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12610 12 ≤ 0.0015 := by
  exact BstLean.Part269.S10.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12610

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12610
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560499469175 : ℝ) ≤ plow 12610 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12610) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052864090286)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001390573027) : eMP 12610 0.011 xi bn ≤ 0.001197029103 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12610 : ℝ) * (1 - 0.011))) ≤ 0.000591856160 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001390573027 / (12610 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000591856160 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000591856160 : ℝ) + 3.141593 * 0.052864090286 / (12610 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001197029103 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052864090286)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001390573027) : PiBarMP 12610 12 0.011 xi bn ≤ 0.161831228049 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12610 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037290387864 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.674930042512 : ℝ) ≤ √((12610 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.294256309038 : ℝ) ≤ √(12610 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12610) ≤ 0.124070533265 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037290387864 + 0.052864090286 * 1.772454 / (2 * (111.674930042512 : ℝ))) * (1 + 0.001197029103) +
        8 / (12610 * 112.294256309038) + 0.124070533265 := by gcongr
    _ ≤ (0.161831228049 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052864090286)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001390573027) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282595231816) :
    parallelOracle 12610 0.011 xi bn cd ≤ 0.162828932692 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12610 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12610 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560499469175 : ℝ) ≤ plow 12610 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.294256309038 : ℝ) ≤ √(12610 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282595231816 : ℝ) / (2 * 0.560499469175 * 112.294256309038)) * 0.161831228049 +
        0.282595231816 ^ 2 / (2 * 0.560499469175 * 112.294256309038) := by gcongr
    _ ≤ (0.162828932692 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052864090286) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001390573027)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282595231816) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12610 12610 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560499469175 : ℝ) ≤ plow 12610 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.294256309038 : ℝ) ≤ √(12610 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12610 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12610 Θ 1.22 ≤ 0.011809156974 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.294256309038 := by gcongr <;> linarith
      _ ≤ (0.011809156974 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12610 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12610 12610 0.011 ≤ 0.008512341475 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12610 12610 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12610 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12610 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12610 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12610 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162828932692 + 0.011809156974 + (0.008512341475 : ℝ) *
        (1 + 2 * (0.282595231816 + 0.011809156974) / (0.560499469175 * 112.294256309038))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12610]

end BstLean.Part269.N12610

/-! The original eight local profiles supply actual 12610 moment certificates. -/
namespace BstLean.Part269.N12610
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12610 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12610 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12610 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052864090286 ∧
    0 ≤ bN 12610 BstLean.Part154.csC (groupTheta g) ∧ bN 12610 BstLean.Part154.csC (groupTheta g) ≤ 0.001390573027 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12610 12610 0.011
      (momentAllowance 12610 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12610 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12610 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12610 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12610 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12610 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229921922152 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12610 0.011
      (momentAllowance 12610 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12610 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12610
/-! The actual computed-centre upper energy formula at 12610. -/
namespace BstLean.Part269.N12610
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12610

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12610
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12610)
open BstLean.Part268 (cell12610)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085757250059
  | 2 => 0.086705008809
  | 3 => 0.087651654667
  | 4 => 0.088598776664
  | 5 => 0.089548290960
  | 6 => 0.090502488665
  | 7 => 0.091464088025
  | 8 => 0.092436290975
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12610 12610 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12610 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12610

/-! Actual upper energy certificates on all 43 source endpoints at 12610. -/
namespace BstLean.Part269.N12610
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12610)
open BstLean.Part268 (cell12610)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12610 (gMinus 12610) (1 - (cell12610 i).lower) ≤ 1 ∧
    energyUpper 12610 (gMinus 12610) (BstLean.Part211.gPlus 12610)
      (finiteEnergy 12610 12610 0.011) (1 - (cell12610 i).lower) ≤
      (cell12610 i).energy := by
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
      have E := BstLean.Part269.S10.uniformEnergy10 (n := 12610) (by norm_num)
        (q := 1 - (cell12610 ⟨10,by decide⟩).lower)
        (by norm_num [cell12610]) (by norm_num [cell12610])
      exact ⟨E.1,E.2.trans (by norm_num [cell12610])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy11 (n := 12610) (by norm_num)
        (q := 1 - (cell12610 ⟨11,by decide⟩).lower)
        (by norm_num [cell12610]) (by norm_num [cell12610])
      exact ⟨E.1,E.2.trans (by norm_num [cell12610])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy12 (n := 12610) (by norm_num)
        (q := 1 - (cell12610 ⟨12,by decide⟩).lower)
        (by norm_num [cell12610]) (by norm_num [cell12610])
      exact ⟨E.1,E.2.trans (by norm_num [cell12610])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy13 (n := 12610) (by norm_num)
        (q := 1 - (cell12610 ⟨13,by decide⟩).lower)
        (by norm_num [cell12610]) (by norm_num [cell12610])
      exact ⟨E.1,E.2.trans (by norm_num [cell12610])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy14 (n := 12610) (by norm_num)
        (q := 1 - (cell12610 ⟨14,by decide⟩).lower)
        (by norm_num [cell12610]) (by norm_num [cell12610])
      exact ⟨E.1,E.2.trans (by norm_num [cell12610])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy15 (n := 12610) (by norm_num)
        (q := 1 - (cell12610 ⟨15,by decide⟩).lower)
        (by norm_num [cell12610]) (by norm_num [cell12610])
      exact ⟨E.1,E.2.trans (by norm_num [cell12610])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy16 (n := 12610) (by norm_num)
        (q := 1 - (cell12610 ⟨16,by decide⟩).lower)
        (by norm_num [cell12610]) (by norm_num [cell12610])
      exact ⟨E.1,E.2.trans (by norm_num [cell12610])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy17 (n := 12610) (by norm_num)
        (q := 1 - (cell12610 ⟨17,by decide⟩).lower)
        (by norm_num [cell12610]) (by norm_num [cell12610])
      exact ⟨E.1,E.2.trans (by norm_num [cell12610])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy18 (n := 12610) (by norm_num)
        (q := 1 - (cell12610 ⟨18,by decide⟩).lower)
        (by norm_num [cell12610]) (by norm_num [cell12610])
      exact ⟨E.1,E.2.trans (by norm_num [cell12610])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy19 (n := 12610) (by norm_num)
        (q := 1 - (cell12610 ⟨19,by decide⟩).lower)
        (by norm_num [cell12610]) (by norm_num [cell12610])
      exact ⟨E.1,E.2.trans (by norm_num [cell12610])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy20 (n := 12610) (by norm_num)
        (q := 1 - (cell12610 ⟨20,by decide⟩).lower)
        (by norm_num [cell12610]) (by norm_num [cell12610])
      exact ⟨E.1,E.2.trans (by norm_num [cell12610])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy21 (n := 12610) (by norm_num)
        (q := 1 - (cell12610 ⟨21,by decide⟩).lower)
        (by norm_num [cell12610]) (by norm_num [cell12610])
      exact ⟨E.1,E.2.trans (by norm_num [cell12610])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy22 (n := 12610) (by norm_num)
        (q := 1 - (cell12610 ⟨22,by decide⟩).lower)
        (by norm_num [cell12610]) (by norm_num [cell12610])
      exact ⟨E.1,E.2.trans (by norm_num [cell12610])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy23 (n := 12610) (by norm_num)
        (q := 1 - (cell12610 ⟨23,by decide⟩).lower)
        (by norm_num [cell12610]) (by norm_num [cell12610])
      exact ⟨E.1,E.2.trans (by norm_num [cell12610])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy24 (n := 12610) (by norm_num)
        (q := 1 - (cell12610 ⟨24,by decide⟩).lower)
        (by norm_num [cell12610]) (by norm_num [cell12610])
      exact ⟨E.1,E.2.trans (by norm_num [cell12610])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy25 (n := 12610) (by norm_num)
        (q := 1 - (cell12610 ⟨25,by decide⟩).lower)
        (by norm_num [cell12610]) (by norm_num [cell12610])
      exact ⟨E.1,E.2.trans (by norm_num [cell12610])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy26 (n := 12610) (by norm_num)
        (q := 1 - (cell12610 ⟨26,by decide⟩).lower)
        (by norm_num [cell12610]) (by norm_num [cell12610])
      exact ⟨E.1,E.2.trans (by norm_num [cell12610])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy27 (n := 12610) (by norm_num)
        (q := 1 - (cell12610 ⟨27,by decide⟩).lower)
        (by norm_num [cell12610]) (by norm_num [cell12610])
      exact ⟨E.1,E.2.trans (by norm_num [cell12610])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy28 (n := 12610) (by norm_num)
        (q := 1 - (cell12610 ⟨28,by decide⟩).lower)
        (by norm_num [cell12610]) (by norm_num [cell12610])
      exact ⟨E.1,E.2.trans (by norm_num [cell12610])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy29 (n := 12610) (by norm_num)
        (q := 1 - (cell12610 ⟨29,by decide⟩).lower)
        (by norm_num [cell12610]) (by norm_num [cell12610])
      exact ⟨E.1,E.2.trans (by norm_num [cell12610])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy30 (n := 12610) (by norm_num)
        (q := 1 - (cell12610 ⟨30,by decide⟩).lower)
        (by norm_num [cell12610]) (by norm_num [cell12610])
      exact ⟨E.1,E.2.trans (by norm_num [cell12610])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy31 (n := 12610) (by norm_num)
        (q := 1 - (cell12610 ⟨31,by decide⟩).lower)
        (by norm_num [cell12610]) (by norm_num [cell12610])
      exact ⟨E.1,E.2.trans (by norm_num [cell12610])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy32 (n := 12610) (by norm_num)
        (q := 1 - (cell12610 ⟨32,by decide⟩).lower)
        (by norm_num [cell12610]) (by norm_num [cell12610])
      exact ⟨E.1,E.2.trans (by norm_num [cell12610])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy33 (n := 12610) (by norm_num)
        (q := 1 - (cell12610 ⟨33,by decide⟩).lower)
        (by norm_num [cell12610]) (by norm_num [cell12610])
      exact ⟨E.1,E.2.trans (by norm_num [cell12610])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy34 (n := 12610) (by norm_num)
        (q := 1 - (cell12610 ⟨34,by decide⟩).lower)
        (by norm_num [cell12610]) (by norm_num [cell12610])
      exact ⟨E.1,E.2.trans (by norm_num [cell12610])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy35 (n := 12610) (by norm_num)
        (q := 1 - (cell12610 ⟨35,by decide⟩).lower)
        (by norm_num [cell12610]) (by norm_num [cell12610])
      exact ⟨E.1,E.2.trans (by norm_num [cell12610])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy36 (n := 12610) (by norm_num)
        (q := 1 - (cell12610 ⟨36,by decide⟩).lower)
        (by norm_num [cell12610]) (by norm_num [cell12610])
      exact ⟨E.1,E.2.trans (by norm_num [cell12610])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy37 (n := 12610) (by norm_num)
        (q := 1 - (cell12610 ⟨37,by decide⟩).lower)
        (by norm_num [cell12610]) (by norm_num [cell12610])
      exact ⟨E.1,E.2.trans (by norm_num [cell12610])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy38 (n := 12610) (by norm_num)
        (q := 1 - (cell12610 ⟨38,by decide⟩).lower)
        (by norm_num [cell12610]) (by norm_num [cell12610])
      exact ⟨E.1,E.2.trans (by norm_num [cell12610])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy39 (n := 12610) (by norm_num)
        (q := 1 - (cell12610 ⟨39,by decide⟩).lower)
        (by norm_num [cell12610]) (by norm_num [cell12610])
      exact ⟨E.1,E.2.trans (by norm_num [cell12610])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy40 (n := 12610) (by norm_num)
        (q := 1 - (cell12610 ⟨40,by decide⟩).lower)
        (by norm_num [cell12610]) (by norm_num [cell12610])
      exact ⟨E.1,E.2.trans (by norm_num [cell12610])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy41 (n := 12610) (by norm_num)
        (q := 1 - (cell12610 ⟨41,by decide⟩).lower)
        (by norm_num [cell12610]) (by norm_num [cell12610])
      exact ⟨E.1,E.2.trans (by norm_num [cell12610])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy42 (n := 12610) (by norm_num)
        (q := 1 - (cell12610 ⟨42,by decide⟩).lower)
        (by norm_num [cell12610]) (by norm_num [cell12610])
      exact ⟨E.1,E.2.trans (by norm_num [cell12610])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy43 (n := 12610) (by norm_num)
        (q := 1 - (cell12610 ⟨43,by decide⟩).lower)
        (by norm_num [cell12610]) (by norm_num [cell12610])
      exact ⟨E.1,E.2.trans (by norm_num [cell12610])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy44 (n := 12610) (by norm_num)
        (q := 1 - (cell12610 ⟨44,by decide⟩).lower)
        (by norm_num [cell12610]) (by norm_num [cell12610])
      exact ⟨E.1,E.2.trans (by norm_num [cell12610])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy45 (n := 12610) (by norm_num)
        (q := 1 - (cell12610 ⟨45,by decide⟩).lower)
        (by norm_num [cell12610]) (by norm_num [cell12610])
      exact ⟨E.1,E.2.trans (by norm_num [cell12610])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy46 (n := 12610) (by norm_num)
        (q := 1 - (cell12610 ⟨46,by decide⟩).lower)
        (by norm_num [cell12610]) (by norm_num [cell12610])
      exact ⟨E.1,E.2.trans (by norm_num [cell12610])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy47 (n := 12610) (by norm_num)
        (q := 1 - (cell12610 ⟨47,by decide⟩).lower)
        (by norm_num [cell12610]) (by norm_num [cell12610])
      exact ⟨E.1,E.2.trans (by norm_num [cell12610])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy48 (n := 12610) (by norm_num)
        (q := 1 - (cell12610 ⟨48,by decide⟩).lower)
        (by norm_num [cell12610]) (by norm_num [cell12610])
      exact ⟨E.1,E.2.trans (by norm_num [cell12610])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy49 (n := 12610) (by norm_num)
        (q := 1 - (cell12610 ⟨49,by decide⟩).lower)
        (by norm_num [cell12610]) (by norm_num [cell12610])
      exact ⟨E.1,E.2.trans (by norm_num [cell12610])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy50 (n := 12610) (by norm_num)
        (q := 1 - (cell12610 ⟨50,by decide⟩).lower)
        (by norm_num [cell12610]) (by norm_num [cell12610])
      exact ⟨E.1,E.2.trans (by norm_num [cell12610])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy51 (n := 12610) (by norm_num)
        (q := 1 - (cell12610 ⟨51,by decide⟩).lower)
        (by norm_num [cell12610]) (by norm_num [cell12610])
      exact ⟨E.1,E.2.trans (by norm_num [cell12610])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy52 (n := 12610) (by norm_num)
        (q := 1 - (cell12610 ⟨52,by decide⟩).lower)
        (by norm_num [cell12610]) (by norm_num [cell12610])
      exact ⟨E.1,E.2.trans (by norm_num [cell12610])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12610

/-! Source-cell containment and simple scalar guards at 12610. -/
namespace BstLean.Part269.N12610
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12610)
open BstLean.Part268 (cell12610)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12610 ⟨10,by decide⟩).lower ∧ (cell12610 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12610 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12610 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12610 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12610 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12610 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12610,cell12610,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12610 ⟨11,by decide⟩).lower ∧ (cell12610 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12610 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12610 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12610 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12610 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12610 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12610,cell12610,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12610 ⟨12,by decide⟩).lower ∧ (cell12610 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12610 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12610 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12610 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12610 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12610 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12610,cell12610,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12610 ⟨13,by decide⟩).lower ∧ (cell12610 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12610 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12610 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12610 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12610 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12610 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12610,cell12610,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12610 ⟨14,by decide⟩).lower ∧ (cell12610 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12610 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12610 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12610 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12610 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12610 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12610,cell12610,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12610 ⟨15,by decide⟩).lower ∧ (cell12610 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12610 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12610 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12610 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12610 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12610 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12610,cell12610,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12610 ⟨16,by decide⟩).lower ∧ (cell12610 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12610 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12610 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12610 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12610 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12610 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12610,cell12610,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12610 ⟨17,by decide⟩).lower ∧ (cell12610 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12610 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12610 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12610 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12610 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12610 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12610,cell12610,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12610 ⟨18,by decide⟩).lower ∧ (cell12610 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12610 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12610 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12610 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12610 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12610 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12610,cell12610,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12610 ⟨19,by decide⟩).lower ∧ (cell12610 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12610 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12610 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12610 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12610 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12610 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12610,cell12610,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12610 ⟨20,by decide⟩).lower ∧ (cell12610 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12610 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12610 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12610 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12610 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12610 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12610,cell12610,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12610 ⟨21,by decide⟩).lower ∧ (cell12610 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12610 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12610 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12610 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12610 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12610 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12610,cell12610,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12610 ⟨22,by decide⟩).lower ∧ (cell12610 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12610 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12610 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12610 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12610 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12610 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12610,cell12610,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12610 ⟨23,by decide⟩).lower ∧ (cell12610 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12610 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12610 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12610 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12610 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12610 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12610,cell12610,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12610 ⟨24,by decide⟩).lower ∧ (cell12610 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12610 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12610 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12610 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12610 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12610 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12610,cell12610,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12610 ⟨25,by decide⟩).lower ∧ (cell12610 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12610 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12610 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12610 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12610 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12610 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12610,cell12610,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12610 ⟨26,by decide⟩).lower ∧ (cell12610 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12610 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12610 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12610 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12610 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12610 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12610,cell12610,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12610 ⟨27,by decide⟩).lower ∧ (cell12610 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12610 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12610 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12610 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12610 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12610 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12610,cell12610,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12610 ⟨28,by decide⟩).lower ∧ (cell12610 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12610 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12610 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12610 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12610 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12610 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12610,cell12610,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12610 ⟨29,by decide⟩).lower ∧ (cell12610 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12610 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12610 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12610 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12610 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12610 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12610,cell12610,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12610 ⟨30,by decide⟩).lower ∧ (cell12610 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12610 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12610 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12610 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12610 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12610 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12610,cell12610,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12610 ⟨31,by decide⟩).lower ∧ (cell12610 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12610 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12610 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12610 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12610 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12610 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12610,cell12610,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12610 ⟨32,by decide⟩).lower ∧ (cell12610 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12610 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12610 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12610 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12610 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12610 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12610,cell12610,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12610 ⟨33,by decide⟩).lower ∧ (cell12610 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12610 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12610 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12610 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12610 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12610 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12610,cell12610,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12610 ⟨34,by decide⟩).lower ∧ (cell12610 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12610 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12610 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12610 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12610 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12610 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12610,cell12610,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12610 ⟨35,by decide⟩).lower ∧ (cell12610 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12610 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12610 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12610 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12610 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12610 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12610,cell12610,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12610 ⟨36,by decide⟩).lower ∧ (cell12610 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12610 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12610 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12610 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12610 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12610 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12610,cell12610,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12610 ⟨37,by decide⟩).lower ∧ (cell12610 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12610 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12610 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12610 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12610 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12610 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12610,cell12610,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12610 ⟨38,by decide⟩).lower ∧ (cell12610 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12610 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12610 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12610 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12610 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12610 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12610,cell12610,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12610 ⟨39,by decide⟩).lower ∧ (cell12610 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12610 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12610 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12610 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12610 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12610 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12610,cell12610,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12610 ⟨40,by decide⟩).lower ∧ (cell12610 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12610 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12610 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12610 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12610 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12610 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12610,cell12610,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12610 ⟨41,by decide⟩).lower ∧ (cell12610 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12610 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12610 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12610 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12610 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12610 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12610,cell12610,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12610 ⟨42,by decide⟩).lower ∧ (cell12610 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12610 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12610 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12610 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12610 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12610 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12610,cell12610,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12610 ⟨43,by decide⟩).lower ∧ (cell12610 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12610 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12610 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12610 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12610 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12610 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12610,cell12610,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12610 ⟨44,by decide⟩).lower ∧ (cell12610 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12610 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12610 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12610 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12610 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12610 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12610,cell12610,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12610 ⟨45,by decide⟩).lower ∧ (cell12610 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12610 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12610 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12610 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12610 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12610 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12610,cell12610,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12610 ⟨46,by decide⟩).lower ∧ (cell12610 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12610 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12610 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12610 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12610 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12610 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12610,cell12610,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12610 ⟨47,by decide⟩).lower ∧ (cell12610 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12610 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12610 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12610 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12610 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12610 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12610,cell12610,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12610 ⟨48,by decide⟩).lower ∧ (cell12610 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12610 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12610 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12610 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12610 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12610 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12610,cell12610,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12610 ⟨49,by decide⟩).lower ∧ (cell12610 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12610 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12610 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12610 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12610 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12610 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12610,cell12610,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12610 ⟨50,by decide⟩).lower ∧ (cell12610 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12610 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12610 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12610 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12610 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12610 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12610,cell12610,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12610 ⟨51,by decide⟩).lower ∧ (cell12610 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12610 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12610 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12610 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12610 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12610 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12610,cell12610,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12610 ⟨52,by decide⟩).lower ∧ (cell12610 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12610 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12610 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12610 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12610 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12610 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12610,cell12610,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12610 i).lower ∧
    (cell12610 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12610 i).upper ≤ (0.532 : ℝ) ∧
    (cell12610 i).centre ≤ (0.1 : ℝ) ∧ (cell12610 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12610 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12610 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12610

/-! The local source numeric instances at 12610 have no network premises. -/
namespace BstLean.Part269.N12610
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12610)
open BstLean.Part268 (cell12610)

noncomputable def sourceNumerics12610 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12610 (cell12610 i)
      scalarRow12610.M scalarRow12610.H scalarRow12610.xi := by
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
    energy_allowance := scalarRow12610.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12610]
    centre_nonneg := (scalarRow12610.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D10.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12610])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12610
/-! Actual 12611 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12611
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12611 ≤ (1.035936470957 : ℝ) := by
  have hr : (112.298708808249 : ℝ) ≤ √(12611 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.298708808249 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12611 12611 (11 / 1000) ≤
    (0.008512003969 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12611) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.298708808249 : ℝ) ≤ √(12611 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12611)
  have hdiv : K / √(12611 : ℝ) ≤ K / 112.298708808249 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.298708808249 ≤ (0.008512003969 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12611.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12611 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12611 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12611 := gPlus_lower 12611
end BstLean.Part269.N12611

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12611
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035936470956 : ℝ) ≤ wn 12611 := by
  have hn : √(12611 : ℝ) ≤ 112.298708808250 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12611 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.298708808250 ≤ 2 / √(12611 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000253689638 : ℝ) ≤ rhoBar 12611 BstLean.Part154.csC ∧
    rhoBar 12611 BstLean.Part154.csC ≤ 0.000253690030 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035936470956 : ℝ) / (1.295212 * 12611) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035936470957 : ℝ) / (1.29521 * 12611) := by gcongr
      _ ≤ (0.000253690030 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12611 BstLean.Part154.csC) ≤ 0.001014824479 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12611 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12611 BstLean.Part154.csC) (piBar (rhoBar 12611 BstLean.Part154.csC)) ≤ 0.000193770221 ∧
    cc1 (rhoBar 12611 BstLean.Part154.csC) (piBar (rhoBar 12611 BstLean.Part154.csC)) ≤ 0.000123297265 ∧
    cc2 (rhoBar 12611 BstLean.Part154.csC) ≤ 0.000071574991 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12611 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12611 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12611 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12611 BstLean.Part154.csC * nuR (rhoBar 12611 BstLean.Part154.csC)) ≤ 0.000507396150 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000253690030 : ℝ) * 0.001014824479 := by gcongr
      _ ≤ (0.000507396150 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12611 BstLean.Part154.csC) * nuR (rhoBar 12611 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001014824479 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12611 BstLean.Part154.csC) * rhoBar 12611 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000253690030 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000253690030 / 2 + 0.399 * 0.001014824479 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000193770221 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000507396150 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123297265 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000253690030 / 1.414213562 := by gcongr
      _ ≤ (0.000071574991 : ℝ) := by norm_num

end BstLean.Part269.N12611

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12611
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12611 BstLean.Part154.csC) (piBar (rhoBar 12611 BstLean.Part154.csC)) ≤ 1.62147E-7 := by
  have hr0 : 0 ≤ rhoBar 12611 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12611 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12611 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12611 BstLean.Part154.csC) (piBar (rhoBar 12611 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12611 BstLean.Part154.csC) (piBar (rhoBar 12611 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12611 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000193770221 : ℝ) ^ 2 + 0.000123297265 ^ 2 + 3 * 0.000071574991 ^ 2 +
        2 * 0.797885 * 0.000193770221 * 0.000123297265 + 2 * 0.000193770221 * 0.000071574991 +
        4 * 0.797885 * 0.000123297265 * 0.000071574991 := by gcongr
    _ ≤ (1.62147E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12611 BstLean.Part154.csC Θ ≤ 0.002648495891 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12611 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12611 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12611 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12611 BstLean.Part154.csC) (piBar (rhoBar 12611 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12611 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035936470957 * 1.62147E-7 / (0.000253689638 : ℝ) := by gcongr
    _ ≤ 0.002648495891 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12611 BstLean.Part154.csC Θ ≤ 0.002939010861 + 0.000669232044 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12611 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12611 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12611 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035936470957 : ℝ) * ((2 * Θ * 0.000253690030 +
        (6863 / 10000) * 0.000253690030 * 12611 * 0.001014824479) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002939010861 + 0.000669232044 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12611 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12611 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12611 0.011 Θ ∧ gammaRatio 12611 0.011 Θ ≤ 0.000087212073 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12611 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035936470957 : ℝ) * 0.525 / ((1 - 0.011) * 12611) := by gcongr
      _ ≤ (0.000087212073 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12611 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12611 0.011 Θ) :=
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
    badAllowance 12611 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000676285396 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12611 BstLean.Part154.csC) 1.22 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 2 (rhoBar 12611 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12611 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12611 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12611 0.011 Θ) 1.12 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 1 (gammaRatio 12611 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12611 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12611 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12611 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12611 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035936470957 : ℝ) * 12611 *
        (2.5110E-8 / 1.1045361 + 3.0670E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000676285396 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12611 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003615296257 + 0.003317727935 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12611

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12611
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12611 BstLean.Part154.csC) (piBar (rhoBar 12611 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12611 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12611 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12611 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12611 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12611 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12611 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12611 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12611 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12611 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12611 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12611 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12611 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12611 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12611 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052671198510 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12611) ≤ 0.010634472950 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12611 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035936470957)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010634472950 + 2 * 0.737676 / 12611) := by gcongr
    _ ≤ (0.052671198510 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12611 12 ≤ 0.0015 := by
  exact BstLean.Part269.S10.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12611

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12611
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560499515042 : ℝ) ≤ plow 12611 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12611) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052863703423)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001390460343) : eMP 12611 0.011 xi bn ≤ 0.001196933058 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12611 : ℝ) * (1 - 0.011))) ≤ 0.000591808714 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001390460343 / (12611 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000591808714 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000591808714 : ℝ) + 3.141593 * 0.052863703423 / (12611 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001196933058 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052863703423)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001390460343) : PiBarMP 12611 12 0.011 xi bn ≤ 0.161824772054 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12611 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037288876935 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.679357985260 : ℝ) ≤ √((12611 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.298708808249 : ℝ) ≤ √(12611 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12611) ≤ 0.124065614028 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037288876935 + 0.052863703423 * 1.772454 / (2 * (111.679357985260 : ℝ))) * (1 + 0.001196933058) +
        8 / (12611 * 112.298708808249) + 0.124065614028 := by gcongr
    _ ≤ (0.161824772054 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052863703423)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001390460343) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282592279369) :
    parallelOracle 12611 0.011 xi bn cd ≤ 0.162822405514 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12611 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12611 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560499515042 : ℝ) ≤ plow 12611 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.298708808249 : ℝ) ≤ √(12611 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282592279369 : ℝ) / (2 * 0.560499515042 * 112.298708808249)) * 0.161824772054 +
        0.282592279369 ^ 2 / (2 * 0.560499515042 * 112.298708808249) := by gcongr
    _ ≤ (0.162822405514 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052863703423) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001390460343)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282592279369) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12611 12611 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560499515042 : ℝ) ≤ plow 12611 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.298708808249 : ℝ) ≤ √(12611 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12611 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12611 Θ 1.22 ≤ 0.011808688756 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.298708808249 := by gcongr <;> linarith
      _ ≤ (0.011808688756 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12611 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12611 12611 0.011 ≤ 0.008512003969 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12611 12611 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12611 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12611 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12611 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12611 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162822405514 + 0.011808688756 + (0.008512003969 : ℝ) *
        (1 + 2 * (0.282592279369 + 0.011808688756) / (0.560499515042 * 112.298708808249))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12611]

end BstLean.Part269.N12611

/-! The original eight local profiles supply actual 12611 moment certificates. -/
namespace BstLean.Part269.N12611
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12611 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12611 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12611 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052863703423 ∧
    0 ≤ bN 12611 BstLean.Part154.csC (groupTheta g) ∧ bN 12611 BstLean.Part154.csC (groupTheta g) ≤ 0.001390460343 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12611 12611 0.011
      (momentAllowance 12611 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12611 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12611 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12611 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12611 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12611 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229921080859 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12611 0.011
      (momentAllowance 12611 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12611 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12611
/-! The actual computed-centre upper energy formula at 12611. -/
namespace BstLean.Part269.N12611
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12611

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12611
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12611)
open BstLean.Part268 (cell12611)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085754232179
  | 2 => 0.086701933128
  | 3 => 0.087648512378
  | 4 => 0.088595556957
  | 5 => 0.089544980677
  | 6 => 0.090499071908
  | 7 => 0.091460545721
  | 8 => 0.092432600392
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12611 12611 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12611 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12611

/-! Actual upper energy certificates on all 43 source endpoints at 12611. -/
namespace BstLean.Part269.N12611
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12611)
open BstLean.Part268 (cell12611)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12611 (gMinus 12611) (1 - (cell12611 i).lower) ≤ 1 ∧
    energyUpper 12611 (gMinus 12611) (BstLean.Part211.gPlus 12611)
      (finiteEnergy 12611 12611 0.011) (1 - (cell12611 i).lower) ≤
      (cell12611 i).energy := by
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
      have E := BstLean.Part269.S10.uniformEnergy10 (n := 12611) (by norm_num)
        (q := 1 - (cell12611 ⟨10,by decide⟩).lower)
        (by norm_num [cell12611]) (by norm_num [cell12611])
      exact ⟨E.1,E.2.trans (by norm_num [cell12611])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy11 (n := 12611) (by norm_num)
        (q := 1 - (cell12611 ⟨11,by decide⟩).lower)
        (by norm_num [cell12611]) (by norm_num [cell12611])
      exact ⟨E.1,E.2.trans (by norm_num [cell12611])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy12 (n := 12611) (by norm_num)
        (q := 1 - (cell12611 ⟨12,by decide⟩).lower)
        (by norm_num [cell12611]) (by norm_num [cell12611])
      exact ⟨E.1,E.2.trans (by norm_num [cell12611])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy13 (n := 12611) (by norm_num)
        (q := 1 - (cell12611 ⟨13,by decide⟩).lower)
        (by norm_num [cell12611]) (by norm_num [cell12611])
      exact ⟨E.1,E.2.trans (by norm_num [cell12611])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy14 (n := 12611) (by norm_num)
        (q := 1 - (cell12611 ⟨14,by decide⟩).lower)
        (by norm_num [cell12611]) (by norm_num [cell12611])
      exact ⟨E.1,E.2.trans (by norm_num [cell12611])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy15 (n := 12611) (by norm_num)
        (q := 1 - (cell12611 ⟨15,by decide⟩).lower)
        (by norm_num [cell12611]) (by norm_num [cell12611])
      exact ⟨E.1,E.2.trans (by norm_num [cell12611])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy16 (n := 12611) (by norm_num)
        (q := 1 - (cell12611 ⟨16,by decide⟩).lower)
        (by norm_num [cell12611]) (by norm_num [cell12611])
      exact ⟨E.1,E.2.trans (by norm_num [cell12611])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy17 (n := 12611) (by norm_num)
        (q := 1 - (cell12611 ⟨17,by decide⟩).lower)
        (by norm_num [cell12611]) (by norm_num [cell12611])
      exact ⟨E.1,E.2.trans (by norm_num [cell12611])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy18 (n := 12611) (by norm_num)
        (q := 1 - (cell12611 ⟨18,by decide⟩).lower)
        (by norm_num [cell12611]) (by norm_num [cell12611])
      exact ⟨E.1,E.2.trans (by norm_num [cell12611])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy19 (n := 12611) (by norm_num)
        (q := 1 - (cell12611 ⟨19,by decide⟩).lower)
        (by norm_num [cell12611]) (by norm_num [cell12611])
      exact ⟨E.1,E.2.trans (by norm_num [cell12611])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy20 (n := 12611) (by norm_num)
        (q := 1 - (cell12611 ⟨20,by decide⟩).lower)
        (by norm_num [cell12611]) (by norm_num [cell12611])
      exact ⟨E.1,E.2.trans (by norm_num [cell12611])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy21 (n := 12611) (by norm_num)
        (q := 1 - (cell12611 ⟨21,by decide⟩).lower)
        (by norm_num [cell12611]) (by norm_num [cell12611])
      exact ⟨E.1,E.2.trans (by norm_num [cell12611])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy22 (n := 12611) (by norm_num)
        (q := 1 - (cell12611 ⟨22,by decide⟩).lower)
        (by norm_num [cell12611]) (by norm_num [cell12611])
      exact ⟨E.1,E.2.trans (by norm_num [cell12611])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy23 (n := 12611) (by norm_num)
        (q := 1 - (cell12611 ⟨23,by decide⟩).lower)
        (by norm_num [cell12611]) (by norm_num [cell12611])
      exact ⟨E.1,E.2.trans (by norm_num [cell12611])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy24 (n := 12611) (by norm_num)
        (q := 1 - (cell12611 ⟨24,by decide⟩).lower)
        (by norm_num [cell12611]) (by norm_num [cell12611])
      exact ⟨E.1,E.2.trans (by norm_num [cell12611])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy25 (n := 12611) (by norm_num)
        (q := 1 - (cell12611 ⟨25,by decide⟩).lower)
        (by norm_num [cell12611]) (by norm_num [cell12611])
      exact ⟨E.1,E.2.trans (by norm_num [cell12611])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy26 (n := 12611) (by norm_num)
        (q := 1 - (cell12611 ⟨26,by decide⟩).lower)
        (by norm_num [cell12611]) (by norm_num [cell12611])
      exact ⟨E.1,E.2.trans (by norm_num [cell12611])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy27 (n := 12611) (by norm_num)
        (q := 1 - (cell12611 ⟨27,by decide⟩).lower)
        (by norm_num [cell12611]) (by norm_num [cell12611])
      exact ⟨E.1,E.2.trans (by norm_num [cell12611])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy28 (n := 12611) (by norm_num)
        (q := 1 - (cell12611 ⟨28,by decide⟩).lower)
        (by norm_num [cell12611]) (by norm_num [cell12611])
      exact ⟨E.1,E.2.trans (by norm_num [cell12611])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy29 (n := 12611) (by norm_num)
        (q := 1 - (cell12611 ⟨29,by decide⟩).lower)
        (by norm_num [cell12611]) (by norm_num [cell12611])
      exact ⟨E.1,E.2.trans (by norm_num [cell12611])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy30 (n := 12611) (by norm_num)
        (q := 1 - (cell12611 ⟨30,by decide⟩).lower)
        (by norm_num [cell12611]) (by norm_num [cell12611])
      exact ⟨E.1,E.2.trans (by norm_num [cell12611])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy31 (n := 12611) (by norm_num)
        (q := 1 - (cell12611 ⟨31,by decide⟩).lower)
        (by norm_num [cell12611]) (by norm_num [cell12611])
      exact ⟨E.1,E.2.trans (by norm_num [cell12611])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy32 (n := 12611) (by norm_num)
        (q := 1 - (cell12611 ⟨32,by decide⟩).lower)
        (by norm_num [cell12611]) (by norm_num [cell12611])
      exact ⟨E.1,E.2.trans (by norm_num [cell12611])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy33 (n := 12611) (by norm_num)
        (q := 1 - (cell12611 ⟨33,by decide⟩).lower)
        (by norm_num [cell12611]) (by norm_num [cell12611])
      exact ⟨E.1,E.2.trans (by norm_num [cell12611])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy34 (n := 12611) (by norm_num)
        (q := 1 - (cell12611 ⟨34,by decide⟩).lower)
        (by norm_num [cell12611]) (by norm_num [cell12611])
      exact ⟨E.1,E.2.trans (by norm_num [cell12611])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy35 (n := 12611) (by norm_num)
        (q := 1 - (cell12611 ⟨35,by decide⟩).lower)
        (by norm_num [cell12611]) (by norm_num [cell12611])
      exact ⟨E.1,E.2.trans (by norm_num [cell12611])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy36 (n := 12611) (by norm_num)
        (q := 1 - (cell12611 ⟨36,by decide⟩).lower)
        (by norm_num [cell12611]) (by norm_num [cell12611])
      exact ⟨E.1,E.2.trans (by norm_num [cell12611])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy37 (n := 12611) (by norm_num)
        (q := 1 - (cell12611 ⟨37,by decide⟩).lower)
        (by norm_num [cell12611]) (by norm_num [cell12611])
      exact ⟨E.1,E.2.trans (by norm_num [cell12611])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy38 (n := 12611) (by norm_num)
        (q := 1 - (cell12611 ⟨38,by decide⟩).lower)
        (by norm_num [cell12611]) (by norm_num [cell12611])
      exact ⟨E.1,E.2.trans (by norm_num [cell12611])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy39 (n := 12611) (by norm_num)
        (q := 1 - (cell12611 ⟨39,by decide⟩).lower)
        (by norm_num [cell12611]) (by norm_num [cell12611])
      exact ⟨E.1,E.2.trans (by norm_num [cell12611])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy40 (n := 12611) (by norm_num)
        (q := 1 - (cell12611 ⟨40,by decide⟩).lower)
        (by norm_num [cell12611]) (by norm_num [cell12611])
      exact ⟨E.1,E.2.trans (by norm_num [cell12611])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy41 (n := 12611) (by norm_num)
        (q := 1 - (cell12611 ⟨41,by decide⟩).lower)
        (by norm_num [cell12611]) (by norm_num [cell12611])
      exact ⟨E.1,E.2.trans (by norm_num [cell12611])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy42 (n := 12611) (by norm_num)
        (q := 1 - (cell12611 ⟨42,by decide⟩).lower)
        (by norm_num [cell12611]) (by norm_num [cell12611])
      exact ⟨E.1,E.2.trans (by norm_num [cell12611])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy43 (n := 12611) (by norm_num)
        (q := 1 - (cell12611 ⟨43,by decide⟩).lower)
        (by norm_num [cell12611]) (by norm_num [cell12611])
      exact ⟨E.1,E.2.trans (by norm_num [cell12611])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy44 (n := 12611) (by norm_num)
        (q := 1 - (cell12611 ⟨44,by decide⟩).lower)
        (by norm_num [cell12611]) (by norm_num [cell12611])
      exact ⟨E.1,E.2.trans (by norm_num [cell12611])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy45 (n := 12611) (by norm_num)
        (q := 1 - (cell12611 ⟨45,by decide⟩).lower)
        (by norm_num [cell12611]) (by norm_num [cell12611])
      exact ⟨E.1,E.2.trans (by norm_num [cell12611])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy46 (n := 12611) (by norm_num)
        (q := 1 - (cell12611 ⟨46,by decide⟩).lower)
        (by norm_num [cell12611]) (by norm_num [cell12611])
      exact ⟨E.1,E.2.trans (by norm_num [cell12611])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy47 (n := 12611) (by norm_num)
        (q := 1 - (cell12611 ⟨47,by decide⟩).lower)
        (by norm_num [cell12611]) (by norm_num [cell12611])
      exact ⟨E.1,E.2.trans (by norm_num [cell12611])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy48 (n := 12611) (by norm_num)
        (q := 1 - (cell12611 ⟨48,by decide⟩).lower)
        (by norm_num [cell12611]) (by norm_num [cell12611])
      exact ⟨E.1,E.2.trans (by norm_num [cell12611])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy49 (n := 12611) (by norm_num)
        (q := 1 - (cell12611 ⟨49,by decide⟩).lower)
        (by norm_num [cell12611]) (by norm_num [cell12611])
      exact ⟨E.1,E.2.trans (by norm_num [cell12611])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy50 (n := 12611) (by norm_num)
        (q := 1 - (cell12611 ⟨50,by decide⟩).lower)
        (by norm_num [cell12611]) (by norm_num [cell12611])
      exact ⟨E.1,E.2.trans (by norm_num [cell12611])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy51 (n := 12611) (by norm_num)
        (q := 1 - (cell12611 ⟨51,by decide⟩).lower)
        (by norm_num [cell12611]) (by norm_num [cell12611])
      exact ⟨E.1,E.2.trans (by norm_num [cell12611])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy52 (n := 12611) (by norm_num)
        (q := 1 - (cell12611 ⟨52,by decide⟩).lower)
        (by norm_num [cell12611]) (by norm_num [cell12611])
      exact ⟨E.1,E.2.trans (by norm_num [cell12611])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12611

/-! Source-cell containment and simple scalar guards at 12611. -/
namespace BstLean.Part269.N12611
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12611)
open BstLean.Part268 (cell12611)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12611 ⟨10,by decide⟩).lower ∧ (cell12611 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12611 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12611 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12611 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12611 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12611 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12611,cell12611,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12611 ⟨11,by decide⟩).lower ∧ (cell12611 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12611 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12611 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12611 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12611 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12611 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12611,cell12611,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12611 ⟨12,by decide⟩).lower ∧ (cell12611 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12611 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12611 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12611 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12611 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12611 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12611,cell12611,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12611 ⟨13,by decide⟩).lower ∧ (cell12611 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12611 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12611 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12611 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12611 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12611 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12611,cell12611,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12611 ⟨14,by decide⟩).lower ∧ (cell12611 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12611 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12611 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12611 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12611 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12611 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12611,cell12611,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12611 ⟨15,by decide⟩).lower ∧ (cell12611 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12611 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12611 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12611 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12611 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12611 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12611,cell12611,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12611 ⟨16,by decide⟩).lower ∧ (cell12611 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12611 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12611 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12611 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12611 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12611 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12611,cell12611,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12611 ⟨17,by decide⟩).lower ∧ (cell12611 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12611 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12611 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12611 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12611 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12611 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12611,cell12611,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12611 ⟨18,by decide⟩).lower ∧ (cell12611 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12611 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12611 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12611 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12611 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12611 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12611,cell12611,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12611 ⟨19,by decide⟩).lower ∧ (cell12611 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12611 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12611 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12611 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12611 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12611 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12611,cell12611,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12611 ⟨20,by decide⟩).lower ∧ (cell12611 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12611 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12611 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12611 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12611 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12611 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12611,cell12611,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12611 ⟨21,by decide⟩).lower ∧ (cell12611 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12611 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12611 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12611 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12611 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12611 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12611,cell12611,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12611 ⟨22,by decide⟩).lower ∧ (cell12611 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12611 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12611 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12611 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12611 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12611 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12611,cell12611,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12611 ⟨23,by decide⟩).lower ∧ (cell12611 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12611 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12611 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12611 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12611 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12611 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12611,cell12611,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12611 ⟨24,by decide⟩).lower ∧ (cell12611 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12611 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12611 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12611 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12611 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12611 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12611,cell12611,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12611 ⟨25,by decide⟩).lower ∧ (cell12611 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12611 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12611 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12611 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12611 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12611 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12611,cell12611,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12611 ⟨26,by decide⟩).lower ∧ (cell12611 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12611 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12611 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12611 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12611 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12611 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12611,cell12611,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12611 ⟨27,by decide⟩).lower ∧ (cell12611 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12611 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12611 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12611 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12611 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12611 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12611,cell12611,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12611 ⟨28,by decide⟩).lower ∧ (cell12611 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12611 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12611 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12611 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12611 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12611 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12611,cell12611,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12611 ⟨29,by decide⟩).lower ∧ (cell12611 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12611 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12611 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12611 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12611 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12611 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12611,cell12611,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12611 ⟨30,by decide⟩).lower ∧ (cell12611 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12611 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12611 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12611 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12611 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12611 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12611,cell12611,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12611 ⟨31,by decide⟩).lower ∧ (cell12611 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12611 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12611 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12611 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12611 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12611 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12611,cell12611,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12611 ⟨32,by decide⟩).lower ∧ (cell12611 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12611 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12611 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12611 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12611 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12611 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12611,cell12611,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12611 ⟨33,by decide⟩).lower ∧ (cell12611 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12611 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12611 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12611 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12611 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12611 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12611,cell12611,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12611 ⟨34,by decide⟩).lower ∧ (cell12611 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12611 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12611 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12611 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12611 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12611 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12611,cell12611,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12611 ⟨35,by decide⟩).lower ∧ (cell12611 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12611 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12611 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12611 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12611 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12611 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12611,cell12611,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12611 ⟨36,by decide⟩).lower ∧ (cell12611 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12611 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12611 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12611 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12611 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12611 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12611,cell12611,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12611 ⟨37,by decide⟩).lower ∧ (cell12611 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12611 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12611 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12611 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12611 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12611 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12611,cell12611,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12611 ⟨38,by decide⟩).lower ∧ (cell12611 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12611 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12611 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12611 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12611 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12611 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12611,cell12611,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12611 ⟨39,by decide⟩).lower ∧ (cell12611 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12611 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12611 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12611 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12611 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12611 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12611,cell12611,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12611 ⟨40,by decide⟩).lower ∧ (cell12611 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12611 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12611 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12611 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12611 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12611 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12611,cell12611,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12611 ⟨41,by decide⟩).lower ∧ (cell12611 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12611 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12611 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12611 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12611 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12611 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12611,cell12611,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12611 ⟨42,by decide⟩).lower ∧ (cell12611 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12611 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12611 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12611 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12611 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12611 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12611,cell12611,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12611 ⟨43,by decide⟩).lower ∧ (cell12611 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12611 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12611 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12611 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12611 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12611 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12611,cell12611,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12611 ⟨44,by decide⟩).lower ∧ (cell12611 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12611 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12611 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12611 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12611 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12611 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12611,cell12611,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12611 ⟨45,by decide⟩).lower ∧ (cell12611 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12611 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12611 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12611 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12611 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12611 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12611,cell12611,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12611 ⟨46,by decide⟩).lower ∧ (cell12611 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12611 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12611 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12611 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12611 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12611 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12611,cell12611,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12611 ⟨47,by decide⟩).lower ∧ (cell12611 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12611 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12611 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12611 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12611 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12611 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12611,cell12611,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12611 ⟨48,by decide⟩).lower ∧ (cell12611 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12611 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12611 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12611 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12611 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12611 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12611,cell12611,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12611 ⟨49,by decide⟩).lower ∧ (cell12611 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12611 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12611 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12611 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12611 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12611 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12611,cell12611,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12611 ⟨50,by decide⟩).lower ∧ (cell12611 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12611 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12611 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12611 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12611 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12611 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12611,cell12611,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12611 ⟨51,by decide⟩).lower ∧ (cell12611 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12611 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12611 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12611 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12611 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12611 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12611,cell12611,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12611 ⟨52,by decide⟩).lower ∧ (cell12611 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12611 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12611 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12611 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12611 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12611 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12611,cell12611,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12611 i).lower ∧
    (cell12611 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12611 i).upper ≤ (0.532 : ℝ) ∧
    (cell12611 i).centre ≤ (0.1 : ℝ) ∧ (cell12611 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12611 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12611 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12611

/-! The local source numeric instances at 12611 have no network premises. -/
namespace BstLean.Part269.N12611
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12611)
open BstLean.Part268 (cell12611)

noncomputable def sourceNumerics12611 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12611 (cell12611 i)
      scalarRow12611.M scalarRow12611.H scalarRow12611.xi := by
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
    energy_allowance := scalarRow12611.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12611]
    centre_nonneg := (scalarRow12611.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D10.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12611])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12611
/-! Actual 12612 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12612
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12612 ≤ (1.035935033661 : ℝ) := by
  have hr : (112.303161130931 : ℝ) ≤ √(12612 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.303161130931 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12612 12612 (11 / 1000) ≤
    (0.008511666503 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12612) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.303161130931 : ℝ) ≤ √(12612 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12612)
  have hdiv : K / √(12612 : ℝ) ≤ K / 112.303161130931 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.303161130931 ≤ (0.008511666503 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12612.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12612 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12612 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12612 := gPlus_lower 12612
end BstLean.Part269.N12612

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12612
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035935033660 : ℝ) ≤ wn 12612 := by
  have hn : √(12612 : ℝ) ≤ 112.303161130932 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12612 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.303161130932 ≤ 2 / √(12612 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000253669171 : ℝ) ≤ rhoBar 12612 BstLean.Part154.csC ∧
    rhoBar 12612 BstLean.Part154.csC ≤ 0.000253669564 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035935033660 : ℝ) / (1.295212 * 12612) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035935033661 : ℝ) / (1.29521 * 12612) := by gcongr
      _ ≤ (0.000253669564 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12612 BstLean.Part154.csC) ≤ 0.001014742605 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12612 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12612 BstLean.Part154.csC) (piBar (rhoBar 12612 BstLean.Part154.csC)) ≤ 0.000193754588 ∧
    cc1 (rhoBar 12612 BstLean.Part154.csC) (piBar (rhoBar 12612 BstLean.Part154.csC)) ≤ 0.000123287318 ∧
    cc2 (rhoBar 12612 BstLean.Part154.csC) ≤ 0.000071569217 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12612 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12612 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12612 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12612 BstLean.Part154.csC * nuR (rhoBar 12612 BstLean.Part154.csC)) ≤ 0.000507355215 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000253669564 : ℝ) * 0.001014742605 := by gcongr
      _ ≤ (0.000507355215 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12612 BstLean.Part154.csC) * nuR (rhoBar 12612 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001014742605 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12612 BstLean.Part154.csC) * rhoBar 12612 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000253669564 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000253669564 / 2 + 0.399 * 0.001014742605 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000193754588 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000507355215 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123287318 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000253669564 / 1.414213562 := by gcongr
      _ ≤ (0.000071569217 : ℝ) := by norm_num

end BstLean.Part269.N12612

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12612
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12612 BstLean.Part154.csC) (piBar (rhoBar 12612 BstLean.Part154.csC)) ≤ 1.62121E-7 := by
  have hr0 : 0 ≤ rhoBar 12612 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12612 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12612 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12612 BstLean.Part154.csC) (piBar (rhoBar 12612 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12612 BstLean.Part154.csC) (piBar (rhoBar 12612 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12612 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000193754588 : ℝ) ^ 2 + 0.000123287318 ^ 2 + 3 * 0.000071569217 ^ 2 +
        2 * 0.797885 * 0.000193754588 * 0.000123287318 + 2 * 0.000193754588 * 0.000071569217 +
        4 * 0.797885 * 0.000123287318 * 0.000071569217 := by gcongr
    _ ≤ (1.62121E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12612 BstLean.Part154.csC Θ ≤ 0.002648281192 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12612 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12612 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12612 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12612 BstLean.Part154.csC) (piBar (rhoBar 12612 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12612 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035935033661 * 1.62121E-7 / (0.000253669171 : ℝ) := by gcongr
    _ ≤ 0.002648281192 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12612 BstLean.Part154.csC Θ ≤ 0.002938765603 + 0.000669177127 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12612 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12612 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12612 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035935033661 : ℝ) * ((2 * Θ * 0.000253669564 +
        (6863 / 10000) * 0.000253669564 * 12612 * 0.001014742605) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002938765603 + 0.000669177127 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12612 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12612 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12612 0.011 Θ ∧ gammaRatio 12612 0.011 Θ ≤ 0.000087205037 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12612 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035935033661 : ℝ) * 0.525 / ((1 - 0.011) * 12612) := by gcongr
      _ ≤ (0.000087205037 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12612 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12612 0.011 Θ) :=
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
    badAllowance 12612 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000676285396 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12612 BstLean.Part154.csC) 1.22 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 2 (rhoBar 12612 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12612 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12612 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12612 0.011 Θ) 1.12 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 1 (gammaRatio 12612 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12612 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12612 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12612 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12612 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035935033661 : ℝ) * 12612 *
        (2.5110E-8 / 1.1045361 + 3.0670E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000676285396 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12612 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003615050999 + 0.003317458319 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12612

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12612
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12612 BstLean.Part154.csC) (piBar (rhoBar 12612 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12612 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12612 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12612 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12612 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12612 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12612 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12612 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12612 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12612 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12612 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12612 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12612 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12612 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12612 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052669087608 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12612) ≤ 0.010634051340 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12612 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035935033661)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010634051340 + 2 * 0.737676 / 12612) := by gcongr
    _ ≤ (0.052669087608 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12612 12 ≤ 0.0015 := by
  exact BstLean.Part269.S10.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12612

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12612
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560499560902 : ℝ) ≤ plow 12612 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12612) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052863316617)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001390347626) : eMP 12612 0.011 xi bn ≤ 0.001196837004 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12612 : ℝ) * (1 - 0.011))) ≤ 0.000591761264 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001390347626 / (12612 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000591761264 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000591761264 : ℝ) + 3.141593 * 0.052863316617 / (12612 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001196837004 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052863316617)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001390347626) : PiBarMP 12612 12 0.011 xi bn ≤ 0.161818316141 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12612 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037287365501 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.683785752453 : ℝ) ≤ √((12612 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.303161130931 : ℝ) ≤ √(12612 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12612) ≤ 0.124060695376 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037287365501 + 0.052863316617 * 1.772454 / (2 * (111.683785752453 : ℝ))) * (1 + 0.001196837004) +
        8 / (12612 * 112.303161130931) + 0.124060695376 := by gcongr
    _ ≤ (0.161818316141 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052863316617)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001390347626) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282589327294) :
    parallelOracle 12612 0.011 xi bn cd ≤ 0.162815878428 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12612 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12612 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560499560902 : ℝ) ≤ plow 12612 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.303161130931 : ℝ) ≤ √(12612 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282589327294 : ℝ) / (2 * 0.560499560902 * 112.303161130931)) * 0.161818316141 +
        0.282589327294 ^ 2 / (2 * 0.560499560902 * 112.303161130931) := by gcongr
    _ ≤ (0.162815878428 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052863316617) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001390347626)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282589327294) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12612 12612 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560499560902 : ℝ) ≤ plow 12612 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.303161130931 : ℝ) ≤ √(12612 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12612 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12612 Θ 1.22 ≤ 0.011808220594 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.303161130931 := by gcongr <;> linarith
      _ ≤ (0.011808220594 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12612 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12612 12612 0.011 ≤ 0.008511666503 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12612 12612 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12612 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12612 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12612 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12612 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162815878428 + 0.011808220594 + (0.008511666503 : ℝ) *
        (1 + 2 * (0.282589327294 + 0.011808220594) / (0.560499560902 * 112.303161130931))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12612]

end BstLean.Part269.N12612

/-! The original eight local profiles supply actual 12612 moment certificates. -/
namespace BstLean.Part269.N12612
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12612 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12612 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12612 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052863316617 ∧
    0 ≤ bN 12612 BstLean.Part154.csC (groupTheta g) ∧ bN 12612 BstLean.Part154.csC (groupTheta g) ≤ 0.001390347626 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12612 12612 0.011
      (momentAllowance 12612 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12612 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12612 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12612 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12612 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12612 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229920239686 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12612 0.011
      (momentAllowance 12612 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12612 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12612
/-! The actual computed-centre upper energy formula at 12612. -/
namespace BstLean.Part269.N12612
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12612

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12612
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12612)
open BstLean.Part268 (cell12612)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085751215488
  | 2 => 0.086698858685
  | 3 => 0.087645371387
  | 4 => 0.088592338625
  | 5 => 0.089541671861
  | 6 => 0.090495656731
  | 7 => 0.091457005132
  | 8 => 0.092428911687
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12612 12612 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12612 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12612

/-! Actual upper energy certificates on all 43 source endpoints at 12612. -/
namespace BstLean.Part269.N12612
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12612)
open BstLean.Part268 (cell12612)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12612 (gMinus 12612) (1 - (cell12612 i).lower) ≤ 1 ∧
    energyUpper 12612 (gMinus 12612) (BstLean.Part211.gPlus 12612)
      (finiteEnergy 12612 12612 0.011) (1 - (cell12612 i).lower) ≤
      (cell12612 i).energy := by
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
      have E := BstLean.Part269.S10.uniformEnergy10 (n := 12612) (by norm_num)
        (q := 1 - (cell12612 ⟨10,by decide⟩).lower)
        (by norm_num [cell12612]) (by norm_num [cell12612])
      exact ⟨E.1,E.2.trans (by norm_num [cell12612])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy11 (n := 12612) (by norm_num)
        (q := 1 - (cell12612 ⟨11,by decide⟩).lower)
        (by norm_num [cell12612]) (by norm_num [cell12612])
      exact ⟨E.1,E.2.trans (by norm_num [cell12612])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy12 (n := 12612) (by norm_num)
        (q := 1 - (cell12612 ⟨12,by decide⟩).lower)
        (by norm_num [cell12612]) (by norm_num [cell12612])
      exact ⟨E.1,E.2.trans (by norm_num [cell12612])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy13 (n := 12612) (by norm_num)
        (q := 1 - (cell12612 ⟨13,by decide⟩).lower)
        (by norm_num [cell12612]) (by norm_num [cell12612])
      exact ⟨E.1,E.2.trans (by norm_num [cell12612])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy14 (n := 12612) (by norm_num)
        (q := 1 - (cell12612 ⟨14,by decide⟩).lower)
        (by norm_num [cell12612]) (by norm_num [cell12612])
      exact ⟨E.1,E.2.trans (by norm_num [cell12612])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy15 (n := 12612) (by norm_num)
        (q := 1 - (cell12612 ⟨15,by decide⟩).lower)
        (by norm_num [cell12612]) (by norm_num [cell12612])
      exact ⟨E.1,E.2.trans (by norm_num [cell12612])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy16 (n := 12612) (by norm_num)
        (q := 1 - (cell12612 ⟨16,by decide⟩).lower)
        (by norm_num [cell12612]) (by norm_num [cell12612])
      exact ⟨E.1,E.2.trans (by norm_num [cell12612])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy17 (n := 12612) (by norm_num)
        (q := 1 - (cell12612 ⟨17,by decide⟩).lower)
        (by norm_num [cell12612]) (by norm_num [cell12612])
      exact ⟨E.1,E.2.trans (by norm_num [cell12612])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy18 (n := 12612) (by norm_num)
        (q := 1 - (cell12612 ⟨18,by decide⟩).lower)
        (by norm_num [cell12612]) (by norm_num [cell12612])
      exact ⟨E.1,E.2.trans (by norm_num [cell12612])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy19 (n := 12612) (by norm_num)
        (q := 1 - (cell12612 ⟨19,by decide⟩).lower)
        (by norm_num [cell12612]) (by norm_num [cell12612])
      exact ⟨E.1,E.2.trans (by norm_num [cell12612])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy20 (n := 12612) (by norm_num)
        (q := 1 - (cell12612 ⟨20,by decide⟩).lower)
        (by norm_num [cell12612]) (by norm_num [cell12612])
      exact ⟨E.1,E.2.trans (by norm_num [cell12612])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy21 (n := 12612) (by norm_num)
        (q := 1 - (cell12612 ⟨21,by decide⟩).lower)
        (by norm_num [cell12612]) (by norm_num [cell12612])
      exact ⟨E.1,E.2.trans (by norm_num [cell12612])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy22 (n := 12612) (by norm_num)
        (q := 1 - (cell12612 ⟨22,by decide⟩).lower)
        (by norm_num [cell12612]) (by norm_num [cell12612])
      exact ⟨E.1,E.2.trans (by norm_num [cell12612])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy23 (n := 12612) (by norm_num)
        (q := 1 - (cell12612 ⟨23,by decide⟩).lower)
        (by norm_num [cell12612]) (by norm_num [cell12612])
      exact ⟨E.1,E.2.trans (by norm_num [cell12612])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy24 (n := 12612) (by norm_num)
        (q := 1 - (cell12612 ⟨24,by decide⟩).lower)
        (by norm_num [cell12612]) (by norm_num [cell12612])
      exact ⟨E.1,E.2.trans (by norm_num [cell12612])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy25 (n := 12612) (by norm_num)
        (q := 1 - (cell12612 ⟨25,by decide⟩).lower)
        (by norm_num [cell12612]) (by norm_num [cell12612])
      exact ⟨E.1,E.2.trans (by norm_num [cell12612])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy26 (n := 12612) (by norm_num)
        (q := 1 - (cell12612 ⟨26,by decide⟩).lower)
        (by norm_num [cell12612]) (by norm_num [cell12612])
      exact ⟨E.1,E.2.trans (by norm_num [cell12612])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy27 (n := 12612) (by norm_num)
        (q := 1 - (cell12612 ⟨27,by decide⟩).lower)
        (by norm_num [cell12612]) (by norm_num [cell12612])
      exact ⟨E.1,E.2.trans (by norm_num [cell12612])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy28 (n := 12612) (by norm_num)
        (q := 1 - (cell12612 ⟨28,by decide⟩).lower)
        (by norm_num [cell12612]) (by norm_num [cell12612])
      exact ⟨E.1,E.2.trans (by norm_num [cell12612])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy29 (n := 12612) (by norm_num)
        (q := 1 - (cell12612 ⟨29,by decide⟩).lower)
        (by norm_num [cell12612]) (by norm_num [cell12612])
      exact ⟨E.1,E.2.trans (by norm_num [cell12612])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy30 (n := 12612) (by norm_num)
        (q := 1 - (cell12612 ⟨30,by decide⟩).lower)
        (by norm_num [cell12612]) (by norm_num [cell12612])
      exact ⟨E.1,E.2.trans (by norm_num [cell12612])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy31 (n := 12612) (by norm_num)
        (q := 1 - (cell12612 ⟨31,by decide⟩).lower)
        (by norm_num [cell12612]) (by norm_num [cell12612])
      exact ⟨E.1,E.2.trans (by norm_num [cell12612])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy32 (n := 12612) (by norm_num)
        (q := 1 - (cell12612 ⟨32,by decide⟩).lower)
        (by norm_num [cell12612]) (by norm_num [cell12612])
      exact ⟨E.1,E.2.trans (by norm_num [cell12612])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy33 (n := 12612) (by norm_num)
        (q := 1 - (cell12612 ⟨33,by decide⟩).lower)
        (by norm_num [cell12612]) (by norm_num [cell12612])
      exact ⟨E.1,E.2.trans (by norm_num [cell12612])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy34 (n := 12612) (by norm_num)
        (q := 1 - (cell12612 ⟨34,by decide⟩).lower)
        (by norm_num [cell12612]) (by norm_num [cell12612])
      exact ⟨E.1,E.2.trans (by norm_num [cell12612])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy35 (n := 12612) (by norm_num)
        (q := 1 - (cell12612 ⟨35,by decide⟩).lower)
        (by norm_num [cell12612]) (by norm_num [cell12612])
      exact ⟨E.1,E.2.trans (by norm_num [cell12612])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy36 (n := 12612) (by norm_num)
        (q := 1 - (cell12612 ⟨36,by decide⟩).lower)
        (by norm_num [cell12612]) (by norm_num [cell12612])
      exact ⟨E.1,E.2.trans (by norm_num [cell12612])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy37 (n := 12612) (by norm_num)
        (q := 1 - (cell12612 ⟨37,by decide⟩).lower)
        (by norm_num [cell12612]) (by norm_num [cell12612])
      exact ⟨E.1,E.2.trans (by norm_num [cell12612])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy38 (n := 12612) (by norm_num)
        (q := 1 - (cell12612 ⟨38,by decide⟩).lower)
        (by norm_num [cell12612]) (by norm_num [cell12612])
      exact ⟨E.1,E.2.trans (by norm_num [cell12612])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy39 (n := 12612) (by norm_num)
        (q := 1 - (cell12612 ⟨39,by decide⟩).lower)
        (by norm_num [cell12612]) (by norm_num [cell12612])
      exact ⟨E.1,E.2.trans (by norm_num [cell12612])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy40 (n := 12612) (by norm_num)
        (q := 1 - (cell12612 ⟨40,by decide⟩).lower)
        (by norm_num [cell12612]) (by norm_num [cell12612])
      exact ⟨E.1,E.2.trans (by norm_num [cell12612])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy41 (n := 12612) (by norm_num)
        (q := 1 - (cell12612 ⟨41,by decide⟩).lower)
        (by norm_num [cell12612]) (by norm_num [cell12612])
      exact ⟨E.1,E.2.trans (by norm_num [cell12612])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy42 (n := 12612) (by norm_num)
        (q := 1 - (cell12612 ⟨42,by decide⟩).lower)
        (by norm_num [cell12612]) (by norm_num [cell12612])
      exact ⟨E.1,E.2.trans (by norm_num [cell12612])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy43 (n := 12612) (by norm_num)
        (q := 1 - (cell12612 ⟨43,by decide⟩).lower)
        (by norm_num [cell12612]) (by norm_num [cell12612])
      exact ⟨E.1,E.2.trans (by norm_num [cell12612])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy44 (n := 12612) (by norm_num)
        (q := 1 - (cell12612 ⟨44,by decide⟩).lower)
        (by norm_num [cell12612]) (by norm_num [cell12612])
      exact ⟨E.1,E.2.trans (by norm_num [cell12612])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy45 (n := 12612) (by norm_num)
        (q := 1 - (cell12612 ⟨45,by decide⟩).lower)
        (by norm_num [cell12612]) (by norm_num [cell12612])
      exact ⟨E.1,E.2.trans (by norm_num [cell12612])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy46 (n := 12612) (by norm_num)
        (q := 1 - (cell12612 ⟨46,by decide⟩).lower)
        (by norm_num [cell12612]) (by norm_num [cell12612])
      exact ⟨E.1,E.2.trans (by norm_num [cell12612])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy47 (n := 12612) (by norm_num)
        (q := 1 - (cell12612 ⟨47,by decide⟩).lower)
        (by norm_num [cell12612]) (by norm_num [cell12612])
      exact ⟨E.1,E.2.trans (by norm_num [cell12612])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy48 (n := 12612) (by norm_num)
        (q := 1 - (cell12612 ⟨48,by decide⟩).lower)
        (by norm_num [cell12612]) (by norm_num [cell12612])
      exact ⟨E.1,E.2.trans (by norm_num [cell12612])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy49 (n := 12612) (by norm_num)
        (q := 1 - (cell12612 ⟨49,by decide⟩).lower)
        (by norm_num [cell12612]) (by norm_num [cell12612])
      exact ⟨E.1,E.2.trans (by norm_num [cell12612])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy50 (n := 12612) (by norm_num)
        (q := 1 - (cell12612 ⟨50,by decide⟩).lower)
        (by norm_num [cell12612]) (by norm_num [cell12612])
      exact ⟨E.1,E.2.trans (by norm_num [cell12612])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy51 (n := 12612) (by norm_num)
        (q := 1 - (cell12612 ⟨51,by decide⟩).lower)
        (by norm_num [cell12612]) (by norm_num [cell12612])
      exact ⟨E.1,E.2.trans (by norm_num [cell12612])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy52 (n := 12612) (by norm_num)
        (q := 1 - (cell12612 ⟨52,by decide⟩).lower)
        (by norm_num [cell12612]) (by norm_num [cell12612])
      exact ⟨E.1,E.2.trans (by norm_num [cell12612])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12612

/-! Source-cell containment and simple scalar guards at 12612. -/
namespace BstLean.Part269.N12612
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12612)
open BstLean.Part268 (cell12612)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12612 ⟨10,by decide⟩).lower ∧ (cell12612 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12612 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12612 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12612 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12612 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12612 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12612,cell12612,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12612 ⟨11,by decide⟩).lower ∧ (cell12612 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12612 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12612 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12612 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12612 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12612 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12612,cell12612,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12612 ⟨12,by decide⟩).lower ∧ (cell12612 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12612 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12612 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12612 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12612 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12612 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12612,cell12612,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12612 ⟨13,by decide⟩).lower ∧ (cell12612 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12612 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12612 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12612 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12612 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12612 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12612,cell12612,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12612 ⟨14,by decide⟩).lower ∧ (cell12612 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12612 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12612 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12612 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12612 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12612 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12612,cell12612,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12612 ⟨15,by decide⟩).lower ∧ (cell12612 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12612 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12612 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12612 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12612 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12612 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12612,cell12612,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12612 ⟨16,by decide⟩).lower ∧ (cell12612 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12612 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12612 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12612 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12612 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12612 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12612,cell12612,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12612 ⟨17,by decide⟩).lower ∧ (cell12612 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12612 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12612 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12612 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12612 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12612 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12612,cell12612,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12612 ⟨18,by decide⟩).lower ∧ (cell12612 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12612 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12612 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12612 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12612 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12612 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12612,cell12612,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12612 ⟨19,by decide⟩).lower ∧ (cell12612 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12612 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12612 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12612 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12612 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12612 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12612,cell12612,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12612 ⟨20,by decide⟩).lower ∧ (cell12612 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12612 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12612 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12612 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12612 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12612 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12612,cell12612,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12612 ⟨21,by decide⟩).lower ∧ (cell12612 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12612 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12612 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12612 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12612 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12612 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12612,cell12612,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12612 ⟨22,by decide⟩).lower ∧ (cell12612 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12612 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12612 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12612 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12612 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12612 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12612,cell12612,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12612 ⟨23,by decide⟩).lower ∧ (cell12612 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12612 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12612 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12612 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12612 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12612 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12612,cell12612,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12612 ⟨24,by decide⟩).lower ∧ (cell12612 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12612 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12612 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12612 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12612 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12612 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12612,cell12612,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12612 ⟨25,by decide⟩).lower ∧ (cell12612 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12612 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12612 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12612 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12612 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12612 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12612,cell12612,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12612 ⟨26,by decide⟩).lower ∧ (cell12612 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12612 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12612 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12612 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12612 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12612 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12612,cell12612,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12612 ⟨27,by decide⟩).lower ∧ (cell12612 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12612 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12612 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12612 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12612 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12612 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12612,cell12612,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12612 ⟨28,by decide⟩).lower ∧ (cell12612 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12612 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12612 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12612 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12612 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12612 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12612,cell12612,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12612 ⟨29,by decide⟩).lower ∧ (cell12612 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12612 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12612 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12612 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12612 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12612 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12612,cell12612,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12612 ⟨30,by decide⟩).lower ∧ (cell12612 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12612 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12612 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12612 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12612 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12612 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12612,cell12612,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12612 ⟨31,by decide⟩).lower ∧ (cell12612 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12612 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12612 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12612 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12612 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12612 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12612,cell12612,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12612 ⟨32,by decide⟩).lower ∧ (cell12612 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12612 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12612 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12612 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12612 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12612 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12612,cell12612,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12612 ⟨33,by decide⟩).lower ∧ (cell12612 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12612 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12612 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12612 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12612 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12612 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12612,cell12612,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12612 ⟨34,by decide⟩).lower ∧ (cell12612 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12612 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12612 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12612 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12612 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12612 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12612,cell12612,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12612 ⟨35,by decide⟩).lower ∧ (cell12612 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12612 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12612 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12612 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12612 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12612 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12612,cell12612,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12612 ⟨36,by decide⟩).lower ∧ (cell12612 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12612 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12612 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12612 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12612 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12612 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12612,cell12612,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12612 ⟨37,by decide⟩).lower ∧ (cell12612 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12612 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12612 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12612 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12612 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12612 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12612,cell12612,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12612 ⟨38,by decide⟩).lower ∧ (cell12612 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12612 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12612 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12612 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12612 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12612 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12612,cell12612,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12612 ⟨39,by decide⟩).lower ∧ (cell12612 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12612 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12612 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12612 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12612 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12612 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12612,cell12612,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12612 ⟨40,by decide⟩).lower ∧ (cell12612 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12612 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12612 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12612 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12612 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12612 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12612,cell12612,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12612 ⟨41,by decide⟩).lower ∧ (cell12612 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12612 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12612 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12612 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12612 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12612 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12612,cell12612,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12612 ⟨42,by decide⟩).lower ∧ (cell12612 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12612 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12612 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12612 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12612 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12612 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12612,cell12612,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12612 ⟨43,by decide⟩).lower ∧ (cell12612 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12612 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12612 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12612 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12612 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12612 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12612,cell12612,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12612 ⟨44,by decide⟩).lower ∧ (cell12612 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12612 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12612 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12612 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12612 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12612 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12612,cell12612,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12612 ⟨45,by decide⟩).lower ∧ (cell12612 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12612 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12612 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12612 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12612 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12612 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12612,cell12612,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12612 ⟨46,by decide⟩).lower ∧ (cell12612 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12612 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12612 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12612 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12612 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12612 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12612,cell12612,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12612 ⟨47,by decide⟩).lower ∧ (cell12612 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12612 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12612 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12612 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12612 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12612 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12612,cell12612,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12612 ⟨48,by decide⟩).lower ∧ (cell12612 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12612 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12612 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12612 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12612 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12612 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12612,cell12612,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12612 ⟨49,by decide⟩).lower ∧ (cell12612 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12612 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12612 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12612 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12612 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12612 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12612,cell12612,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12612 ⟨50,by decide⟩).lower ∧ (cell12612 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12612 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12612 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12612 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12612 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12612 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12612,cell12612,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12612 ⟨51,by decide⟩).lower ∧ (cell12612 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12612 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12612 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12612 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12612 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12612 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12612,cell12612,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12612 ⟨52,by decide⟩).lower ∧ (cell12612 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12612 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12612 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12612 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12612 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12612 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12612,cell12612,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12612 i).lower ∧
    (cell12612 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12612 i).upper ≤ (0.532 : ℝ) ∧
    (cell12612 i).centre ≤ (0.1 : ℝ) ∧ (cell12612 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12612 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12612 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12612

/-! The local source numeric instances at 12612 have no network premises. -/
namespace BstLean.Part269.N12612
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12612)
open BstLean.Part268 (cell12612)

noncomputable def sourceNumerics12612 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12612 (cell12612 i)
      scalarRow12612.M scalarRow12612.H scalarRow12612.xi := by
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
    energy_allowance := scalarRow12612.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12612]
    centre_nonneg := (scalarRow12612.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D10.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12612])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12612