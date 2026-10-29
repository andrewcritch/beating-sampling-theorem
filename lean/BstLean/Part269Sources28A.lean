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
import BstLean.Part269Direction28
import BstLean.Part269Shared28
import BstLean.Part269Finite
import BstLean.Part269Rows28
import BstLean.Part269Source
/-! Actual 13050 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13050
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13050 ≤ (1.035321562173 : ℝ) := by
  have hr : (114.236596587958 : ℝ) ≤ √(13050 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.236596587958 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13050 13050 (11 / 1000) ≤
    (0.008367606871 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13050) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.236596587958 : ℝ) ≤ √(13050 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13050)
  have hdiv : K / √(13050 : ℝ) ≤ K / 114.236596587958 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.236596587958 ≤ (0.008367606871 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13050.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13050 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13050 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13050 := gPlus_lower 13050
end BstLean.Part269.N13050

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13050
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035321562172 : ℝ) ≤ wn 13050 := by
  have hn : √(13050 : ℝ) ≤ 114.236596587959 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13050 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.236596587959 ≤ 2 / √(13050 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000245010038 : ℝ) ≤ rhoBar 13050 BstLean.Part154.csC ∧
    rhoBar 13050 BstLean.Part154.csC ≤ 0.000245010418 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035321562172 : ℝ) / (1.295212 * 13050) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035321562173 : ℝ) / (1.29521 * 13050) := by gcongr
      _ ≤ (0.000245010418 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13050 BstLean.Part154.csC) ≤ 0.000980101703 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13050 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13050 BstLean.Part154.csC) (piBar (rhoBar 13050 BstLean.Part154.csC)) ≤ 0.000187140373 ∧
    cc1 (rhoBar 13050 BstLean.Part154.csC) (piBar (rhoBar 13050 BstLean.Part154.csC)) ≤ 0.000119078711 ∧
    cc2 (rhoBar 13050 BstLean.Part154.csC) ≤ 0.000069126163 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13050 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13050 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13050 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13050 BstLean.Part154.csC * nuR (rhoBar 13050 BstLean.Part154.csC)) ≤ 0.000490035844 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000245010418 : ℝ) * 0.000980101703 := by gcongr
      _ ≤ (0.000490035844 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13050 BstLean.Part154.csC) * nuR (rhoBar 13050 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000980101703 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13050 BstLean.Part154.csC) * rhoBar 13050 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000245010418 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000245010418 / 2 + 0.399 * 0.000980101703 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000187140373 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000490035844 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119078711 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000245010418 / 1.414213562 := by gcongr
      _ ≤ (0.000069126163 : ℝ) := by norm_num

end BstLean.Part269.N13050

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13050
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13050 BstLean.Part154.csC) (piBar (rhoBar 13050 BstLean.Part154.csC)) ≤ 1.51241E-7 := by
  have hr0 : 0 ≤ rhoBar 13050 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13050 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13050 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13050 BstLean.Part154.csC) (piBar (rhoBar 13050 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13050 BstLean.Part154.csC) (piBar (rhoBar 13050 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13050 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000187140373 : ℝ) ^ 2 + 0.000119078711 ^ 2 + 3 * 0.000069126163 ^ 2 +
        2 * 0.797885 * 0.000187140373 * 0.000119078711 + 2 * 0.000187140373 * 0.000069126163 +
        4 * 0.797885 * 0.000119078711 * 0.000069126163 := by gcongr
    _ ≤ (1.51241E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13050 BstLean.Part154.csC Θ ≤ 0.002556353522 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13050 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13050 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13050 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13050 BstLean.Part154.csC) (piBar (rhoBar 13050 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13050 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035321562173 * 1.51241E-7 / (0.000245010038 : ℝ) := by gcongr
    _ ≤ 0.002556353522 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13050 BstLean.Part154.csC Θ ≤ 0.002835082320 + 0.000645951655 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13050 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13050 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13050 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035321562173 : ℝ) * ((2 * Θ * 0.000245010418 +
        (6863 / 10000) * 0.000245010418 * 13050 * 0.000980101703) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002835082320 + 0.000645951655 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13050 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13050 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13050 0.011 Θ ∧ gammaRatio 13050 0.011 Θ ≤ 0.000084228246 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13050 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035321562173 : ℝ) * 0.525 / ((1 - 0.011) * 13050) := by gcongr
      _ ≤ (0.000084228246 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13050 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13050 0.011 Θ) :=
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
    badAllowance 13050 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000383749387 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13050 BstLean.Part154.csC) 1.22 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 2 (rhoBar 13050 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13050 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13050 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13050 0.011 Θ) 1.12 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 1 (gammaRatio 13050 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13050 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13050 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13050 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13050 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035321562173 : ℝ) * 13050 *
        (1.3781E-8 / 1.1045361 + 1.6832E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000383749387 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13050 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003218831707 + 0.003202305177 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13050

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13050
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13050 BstLean.Part154.csC) (piBar (rhoBar 13050 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13050 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13050 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13050 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13050 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13050 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13050 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13050 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13050 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13050 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13050 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13050 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13050 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13050 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13050 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051768136860 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13050) ≤ 0.010454071784 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13050 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035321562173)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010454071784 + 2 * 0.737676 / 13050) := by gcongr
    _ ≤ (0.051768136860 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13050 12 ≤ 0.0015 := by
  exact BstLean.Part269.S28.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13050

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13050
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560518971823 : ℝ) ≤ plow 13050 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13050) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052406641925)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001342085600) : eMP 13050 0.011 xi bn ≤ 0.001155876017 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13050 : ℝ) * (1 - 0.011))) ≤ 0.000571559789 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001342085600 / (13050 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000571559789 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000571559789 : ℝ) + 3.141593 * 0.052406641925 / (13050 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001155876017 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052406641925)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001342085600) : PiBarMP 13050 12 0.011 xi bn ≤ 0.159052474939 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13050 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036634486485 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.606557909303 : ℝ) ≤ √((13050 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.236596587958 : ℝ) ≤ √(13050 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13050) ≤ 0.121960988676 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036634486485 + 0.052406641925 * 1.772454 / (2 * (113.606557909303 : ℝ))) * (1 + 0.001155876017) +
        8 / (13050 * 114.236596587958) + 0.121960988676 := by gcongr
    _ ≤ (0.159052474939 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052406641925)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001342085600) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280693106938) :
    parallelOracle 13050 0.011 xi bn cd ≤ 0.160016320973 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13050 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13050 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560518971823 : ℝ) ≤ plow 13050 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.236596587958 : ℝ) ≤ √(13050 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280693106938 : ℝ) / (2 * 0.560518971823 * 114.236596587958)) * 0.159052474939 +
        0.280693106938 ^ 2 / (2 * 0.560518971823 * 114.236596587958) := by gcongr
    _ ≤ (0.160016320973 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052406641925) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001342085600)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280693106938) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13050 13050 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560518971823 : ℝ) ≤ plow 13050 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.236596587958 : ℝ) ≤ √(13050 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13050 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13050 Θ 1.22 ≤ 0.011608368418 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.236596587958 := by gcongr <;> linarith
      _ ≤ (0.011608368418 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13050 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13050 13050 0.011 ≤ 0.008367606871 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13050 13050 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13050 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13050 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13050 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13050 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160016320973 + 0.011608368418 + (0.008367606871 : ℝ) *
        (1 + 2 * (0.280693106938 + 0.011608368418) / (0.560518971823 * 114.236596587958))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13050]

end BstLean.Part269.N13050

/-! The original eight local profiles supply actual 13050 moment certificates. -/
namespace BstLean.Part269.N13050
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13050 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13050 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13050 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052406641925 ∧
    0 ≤ bN 13050 BstLean.Part154.csC (groupTheta g) ∧ bN 13050 BstLean.Part154.csC (groupTheta g) ≤ 0.001342085600 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13050 13050 0.011
      (momentAllowance 13050 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13050 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13050 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13050 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13050 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13050 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228924970078 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13050 0.011
      (momentAllowance 13050 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13050 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13050
/-! The actual computed-centre upper energy formula at 13050. -/
namespace BstLean.Part269.N13050
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13050

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13050
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13050)
open BstLean.Part268 (cell13050)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084530178259
  | 2 => 0.085457158408
  | 3 => 0.086380093019
  | 4 => 0.087299886627
  | 5 => 0.088217648246
  | 6 => 0.089134723574
  | 7 => 0.090052730588
  | 8 => 0.090973598625
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13050 13050 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13050 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003218831707 + 0.003202305177 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S28.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13050

/-! Actual upper energy certificates on all 43 source endpoints at 13050. -/
namespace BstLean.Part269.N13050
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13050)
open BstLean.Part268 (cell13050)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13050 (gMinus 13050) (1 - (cell13050 i).lower) ≤ 1 ∧
    energyUpper 13050 (gMinus 13050) (BstLean.Part211.gPlus 13050)
      (finiteEnergy 13050 13050 0.011) (1 - (cell13050 i).lower) ≤
      (cell13050 i).energy := by
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
      have E := BstLean.Part269.S28.uniformEnergy10 (n := 13050) (by norm_num)
        (q := 1 - (cell13050 ⟨10,by decide⟩).lower)
        (by norm_num [cell13050]) (by norm_num [cell13050])
      exact ⟨E.1,E.2.trans (by norm_num [cell13050])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy11 (n := 13050) (by norm_num)
        (q := 1 - (cell13050 ⟨11,by decide⟩).lower)
        (by norm_num [cell13050]) (by norm_num [cell13050])
      exact ⟨E.1,E.2.trans (by norm_num [cell13050])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy12 (n := 13050) (by norm_num)
        (q := 1 - (cell13050 ⟨12,by decide⟩).lower)
        (by norm_num [cell13050]) (by norm_num [cell13050])
      exact ⟨E.1,E.2.trans (by norm_num [cell13050])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy13 (n := 13050) (by norm_num)
        (q := 1 - (cell13050 ⟨13,by decide⟩).lower)
        (by norm_num [cell13050]) (by norm_num [cell13050])
      exact ⟨E.1,E.2.trans (by norm_num [cell13050])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy14 (n := 13050) (by norm_num)
        (q := 1 - (cell13050 ⟨14,by decide⟩).lower)
        (by norm_num [cell13050]) (by norm_num [cell13050])
      exact ⟨E.1,E.2.trans (by norm_num [cell13050])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy15 (n := 13050) (by norm_num)
        (q := 1 - (cell13050 ⟨15,by decide⟩).lower)
        (by norm_num [cell13050]) (by norm_num [cell13050])
      exact ⟨E.1,E.2.trans (by norm_num [cell13050])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy16 (n := 13050) (by norm_num)
        (q := 1 - (cell13050 ⟨16,by decide⟩).lower)
        (by norm_num [cell13050]) (by norm_num [cell13050])
      exact ⟨E.1,E.2.trans (by norm_num [cell13050])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy17 (n := 13050) (by norm_num)
        (q := 1 - (cell13050 ⟨17,by decide⟩).lower)
        (by norm_num [cell13050]) (by norm_num [cell13050])
      exact ⟨E.1,E.2.trans (by norm_num [cell13050])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy18 (n := 13050) (by norm_num)
        (q := 1 - (cell13050 ⟨18,by decide⟩).lower)
        (by norm_num [cell13050]) (by norm_num [cell13050])
      exact ⟨E.1,E.2.trans (by norm_num [cell13050])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy19 (n := 13050) (by norm_num)
        (q := 1 - (cell13050 ⟨19,by decide⟩).lower)
        (by norm_num [cell13050]) (by norm_num [cell13050])
      exact ⟨E.1,E.2.trans (by norm_num [cell13050])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy20 (n := 13050) (by norm_num)
        (q := 1 - (cell13050 ⟨20,by decide⟩).lower)
        (by norm_num [cell13050]) (by norm_num [cell13050])
      exact ⟨E.1,E.2.trans (by norm_num [cell13050])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy21 (n := 13050) (by norm_num)
        (q := 1 - (cell13050 ⟨21,by decide⟩).lower)
        (by norm_num [cell13050]) (by norm_num [cell13050])
      exact ⟨E.1,E.2.trans (by norm_num [cell13050])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy22 (n := 13050) (by norm_num)
        (q := 1 - (cell13050 ⟨22,by decide⟩).lower)
        (by norm_num [cell13050]) (by norm_num [cell13050])
      exact ⟨E.1,E.2.trans (by norm_num [cell13050])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy23 (n := 13050) (by norm_num)
        (q := 1 - (cell13050 ⟨23,by decide⟩).lower)
        (by norm_num [cell13050]) (by norm_num [cell13050])
      exact ⟨E.1,E.2.trans (by norm_num [cell13050])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy24 (n := 13050) (by norm_num)
        (q := 1 - (cell13050 ⟨24,by decide⟩).lower)
        (by norm_num [cell13050]) (by norm_num [cell13050])
      exact ⟨E.1,E.2.trans (by norm_num [cell13050])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy25 (n := 13050) (by norm_num)
        (q := 1 - (cell13050 ⟨25,by decide⟩).lower)
        (by norm_num [cell13050]) (by norm_num [cell13050])
      exact ⟨E.1,E.2.trans (by norm_num [cell13050])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy26 (n := 13050) (by norm_num)
        (q := 1 - (cell13050 ⟨26,by decide⟩).lower)
        (by norm_num [cell13050]) (by norm_num [cell13050])
      exact ⟨E.1,E.2.trans (by norm_num [cell13050])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy27 (n := 13050) (by norm_num)
        (q := 1 - (cell13050 ⟨27,by decide⟩).lower)
        (by norm_num [cell13050]) (by norm_num [cell13050])
      exact ⟨E.1,E.2.trans (by norm_num [cell13050])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy28 (n := 13050) (by norm_num)
        (q := 1 - (cell13050 ⟨28,by decide⟩).lower)
        (by norm_num [cell13050]) (by norm_num [cell13050])
      exact ⟨E.1,E.2.trans (by norm_num [cell13050])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy29 (n := 13050) (by norm_num)
        (q := 1 - (cell13050 ⟨29,by decide⟩).lower)
        (by norm_num [cell13050]) (by norm_num [cell13050])
      exact ⟨E.1,E.2.trans (by norm_num [cell13050])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy30 (n := 13050) (by norm_num)
        (q := 1 - (cell13050 ⟨30,by decide⟩).lower)
        (by norm_num [cell13050]) (by norm_num [cell13050])
      exact ⟨E.1,E.2.trans (by norm_num [cell13050])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy31 (n := 13050) (by norm_num)
        (q := 1 - (cell13050 ⟨31,by decide⟩).lower)
        (by norm_num [cell13050]) (by norm_num [cell13050])
      exact ⟨E.1,E.2.trans (by norm_num [cell13050])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy32 (n := 13050) (by norm_num)
        (q := 1 - (cell13050 ⟨32,by decide⟩).lower)
        (by norm_num [cell13050]) (by norm_num [cell13050])
      exact ⟨E.1,E.2.trans (by norm_num [cell13050])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy33 (n := 13050) (by norm_num)
        (q := 1 - (cell13050 ⟨33,by decide⟩).lower)
        (by norm_num [cell13050]) (by norm_num [cell13050])
      exact ⟨E.1,E.2.trans (by norm_num [cell13050])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy34 (n := 13050) (by norm_num)
        (q := 1 - (cell13050 ⟨34,by decide⟩).lower)
        (by norm_num [cell13050]) (by norm_num [cell13050])
      exact ⟨E.1,E.2.trans (by norm_num [cell13050])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy35 (n := 13050) (by norm_num)
        (q := 1 - (cell13050 ⟨35,by decide⟩).lower)
        (by norm_num [cell13050]) (by norm_num [cell13050])
      exact ⟨E.1,E.2.trans (by norm_num [cell13050])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy36 (n := 13050) (by norm_num)
        (q := 1 - (cell13050 ⟨36,by decide⟩).lower)
        (by norm_num [cell13050]) (by norm_num [cell13050])
      exact ⟨E.1,E.2.trans (by norm_num [cell13050])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy37 (n := 13050) (by norm_num)
        (q := 1 - (cell13050 ⟨37,by decide⟩).lower)
        (by norm_num [cell13050]) (by norm_num [cell13050])
      exact ⟨E.1,E.2.trans (by norm_num [cell13050])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy38 (n := 13050) (by norm_num)
        (q := 1 - (cell13050 ⟨38,by decide⟩).lower)
        (by norm_num [cell13050]) (by norm_num [cell13050])
      exact ⟨E.1,E.2.trans (by norm_num [cell13050])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy39 (n := 13050) (by norm_num)
        (q := 1 - (cell13050 ⟨39,by decide⟩).lower)
        (by norm_num [cell13050]) (by norm_num [cell13050])
      exact ⟨E.1,E.2.trans (by norm_num [cell13050])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy40 (n := 13050) (by norm_num)
        (q := 1 - (cell13050 ⟨40,by decide⟩).lower)
        (by norm_num [cell13050]) (by norm_num [cell13050])
      exact ⟨E.1,E.2.trans (by norm_num [cell13050])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy41 (n := 13050) (by norm_num)
        (q := 1 - (cell13050 ⟨41,by decide⟩).lower)
        (by norm_num [cell13050]) (by norm_num [cell13050])
      exact ⟨E.1,E.2.trans (by norm_num [cell13050])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy42 (n := 13050) (by norm_num)
        (q := 1 - (cell13050 ⟨42,by decide⟩).lower)
        (by norm_num [cell13050]) (by norm_num [cell13050])
      exact ⟨E.1,E.2.trans (by norm_num [cell13050])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy43 (n := 13050) (by norm_num)
        (q := 1 - (cell13050 ⟨43,by decide⟩).lower)
        (by norm_num [cell13050]) (by norm_num [cell13050])
      exact ⟨E.1,E.2.trans (by norm_num [cell13050])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy44 (n := 13050) (by norm_num)
        (q := 1 - (cell13050 ⟨44,by decide⟩).lower)
        (by norm_num [cell13050]) (by norm_num [cell13050])
      exact ⟨E.1,E.2.trans (by norm_num [cell13050])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy45 (n := 13050) (by norm_num)
        (q := 1 - (cell13050 ⟨45,by decide⟩).lower)
        (by norm_num [cell13050]) (by norm_num [cell13050])
      exact ⟨E.1,E.2.trans (by norm_num [cell13050])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy46 (n := 13050) (by norm_num)
        (q := 1 - (cell13050 ⟨46,by decide⟩).lower)
        (by norm_num [cell13050]) (by norm_num [cell13050])
      exact ⟨E.1,E.2.trans (by norm_num [cell13050])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy47 (n := 13050) (by norm_num)
        (q := 1 - (cell13050 ⟨47,by decide⟩).lower)
        (by norm_num [cell13050]) (by norm_num [cell13050])
      exact ⟨E.1,E.2.trans (by norm_num [cell13050])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy48 (n := 13050) (by norm_num)
        (q := 1 - (cell13050 ⟨48,by decide⟩).lower)
        (by norm_num [cell13050]) (by norm_num [cell13050])
      exact ⟨E.1,E.2.trans (by norm_num [cell13050])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy49 (n := 13050) (by norm_num)
        (q := 1 - (cell13050 ⟨49,by decide⟩).lower)
        (by norm_num [cell13050]) (by norm_num [cell13050])
      exact ⟨E.1,E.2.trans (by norm_num [cell13050])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy50 (n := 13050) (by norm_num)
        (q := 1 - (cell13050 ⟨50,by decide⟩).lower)
        (by norm_num [cell13050]) (by norm_num [cell13050])
      exact ⟨E.1,E.2.trans (by norm_num [cell13050])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy51 (n := 13050) (by norm_num)
        (q := 1 - (cell13050 ⟨51,by decide⟩).lower)
        (by norm_num [cell13050]) (by norm_num [cell13050])
      exact ⟨E.1,E.2.trans (by norm_num [cell13050])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy52 (n := 13050) (by norm_num)
        (q := 1 - (cell13050 ⟨52,by decide⟩).lower)
        (by norm_num [cell13050]) (by norm_num [cell13050])
      exact ⟨E.1,E.2.trans (by norm_num [cell13050])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13050

/-! Source-cell containment and simple scalar guards at 13050. -/
namespace BstLean.Part269.N13050
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13050)
open BstLean.Part268 (cell13050)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13050 ⟨10,by decide⟩).lower ∧ (cell13050 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13050 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13050 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13050 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13050 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13050 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13050,cell13050,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13050 ⟨11,by decide⟩).lower ∧ (cell13050 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13050 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13050 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13050 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13050 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13050 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13050,cell13050,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13050 ⟨12,by decide⟩).lower ∧ (cell13050 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13050 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13050 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13050 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13050 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13050 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13050,cell13050,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13050 ⟨13,by decide⟩).lower ∧ (cell13050 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13050 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13050 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13050 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13050 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13050 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13050,cell13050,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13050 ⟨14,by decide⟩).lower ∧ (cell13050 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13050 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13050 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13050 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13050 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13050 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13050,cell13050,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13050 ⟨15,by decide⟩).lower ∧ (cell13050 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13050 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13050 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13050 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13050 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13050 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13050,cell13050,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13050 ⟨16,by decide⟩).lower ∧ (cell13050 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13050 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13050 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13050 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13050 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13050 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13050,cell13050,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13050 ⟨17,by decide⟩).lower ∧ (cell13050 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13050 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13050 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13050 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13050 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13050 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13050,cell13050,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13050 ⟨18,by decide⟩).lower ∧ (cell13050 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13050 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13050 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13050 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13050 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13050 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13050,cell13050,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13050 ⟨19,by decide⟩).lower ∧ (cell13050 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13050 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13050 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13050 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13050 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13050 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13050,cell13050,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13050 ⟨20,by decide⟩).lower ∧ (cell13050 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13050 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13050 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13050 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13050 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13050 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13050,cell13050,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13050 ⟨21,by decide⟩).lower ∧ (cell13050 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13050 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13050 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13050 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13050 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13050 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13050,cell13050,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13050 ⟨22,by decide⟩).lower ∧ (cell13050 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13050 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13050 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13050 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13050 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13050 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13050,cell13050,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13050 ⟨23,by decide⟩).lower ∧ (cell13050 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13050 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13050 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13050 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13050 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13050 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13050,cell13050,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13050 ⟨24,by decide⟩).lower ∧ (cell13050 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13050 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13050 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13050 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13050 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13050 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13050,cell13050,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13050 ⟨25,by decide⟩).lower ∧ (cell13050 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13050 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13050 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13050 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13050 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13050 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13050,cell13050,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13050 ⟨26,by decide⟩).lower ∧ (cell13050 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13050 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13050 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13050 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13050 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13050 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13050,cell13050,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13050 ⟨27,by decide⟩).lower ∧ (cell13050 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13050 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13050 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13050 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13050 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13050 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13050,cell13050,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13050 ⟨28,by decide⟩).lower ∧ (cell13050 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13050 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13050 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13050 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13050 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13050 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13050,cell13050,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13050 ⟨29,by decide⟩).lower ∧ (cell13050 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13050 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13050 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13050 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13050 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13050 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13050,cell13050,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13050 ⟨30,by decide⟩).lower ∧ (cell13050 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13050 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13050 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13050 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13050 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13050 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13050,cell13050,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13050 ⟨31,by decide⟩).lower ∧ (cell13050 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13050 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13050 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13050 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13050 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13050 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13050,cell13050,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13050 ⟨32,by decide⟩).lower ∧ (cell13050 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13050 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13050 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13050 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13050 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13050 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13050,cell13050,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13050 ⟨33,by decide⟩).lower ∧ (cell13050 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13050 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13050 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13050 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13050 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13050 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13050,cell13050,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13050 ⟨34,by decide⟩).lower ∧ (cell13050 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13050 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13050 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13050 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13050 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13050 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13050,cell13050,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13050 ⟨35,by decide⟩).lower ∧ (cell13050 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13050 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13050 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13050 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13050 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13050 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13050,cell13050,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13050 ⟨36,by decide⟩).lower ∧ (cell13050 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13050 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13050 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13050 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13050 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13050 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13050,cell13050,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13050 ⟨37,by decide⟩).lower ∧ (cell13050 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13050 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13050 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13050 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13050 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13050 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13050,cell13050,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13050 ⟨38,by decide⟩).lower ∧ (cell13050 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13050 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13050 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13050 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13050 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13050 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13050,cell13050,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13050 ⟨39,by decide⟩).lower ∧ (cell13050 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13050 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13050 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13050 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13050 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13050 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13050,cell13050,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13050 ⟨40,by decide⟩).lower ∧ (cell13050 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13050 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13050 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13050 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13050 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13050 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13050,cell13050,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13050 ⟨41,by decide⟩).lower ∧ (cell13050 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13050 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13050 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13050 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13050 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13050 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13050,cell13050,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13050 ⟨42,by decide⟩).lower ∧ (cell13050 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13050 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13050 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13050 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13050 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13050 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13050,cell13050,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13050 ⟨43,by decide⟩).lower ∧ (cell13050 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13050 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13050 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13050 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13050 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13050 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13050,cell13050,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13050 ⟨44,by decide⟩).lower ∧ (cell13050 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13050 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13050 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13050 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13050 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13050 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13050,cell13050,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13050 ⟨45,by decide⟩).lower ∧ (cell13050 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13050 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13050 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13050 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13050 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13050 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13050,cell13050,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13050 ⟨46,by decide⟩).lower ∧ (cell13050 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13050 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13050 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13050 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13050 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13050 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13050,cell13050,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13050 ⟨47,by decide⟩).lower ∧ (cell13050 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13050 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13050 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13050 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13050 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13050 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13050,cell13050,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13050 ⟨48,by decide⟩).lower ∧ (cell13050 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13050 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13050 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13050 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13050 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13050 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13050,cell13050,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13050 ⟨49,by decide⟩).lower ∧ (cell13050 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13050 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13050 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13050 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13050 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13050 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13050,cell13050,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13050 ⟨50,by decide⟩).lower ∧ (cell13050 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13050 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13050 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13050 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13050 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13050 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13050,cell13050,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13050 ⟨51,by decide⟩).lower ∧ (cell13050 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13050 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13050 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13050 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13050 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13050 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13050,cell13050,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13050 ⟨52,by decide⟩).lower ∧ (cell13050 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13050 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13050 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13050 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13050 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13050 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13050,cell13050,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13050 i).lower ∧
    (cell13050 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13050 i).upper ≤ (0.532 : ℝ) ∧
    (cell13050 i).centre ≤ (0.1 : ℝ) ∧ (cell13050 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13050 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13050 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13050

/-! The local source numeric instances at 13050 have no network premises. -/
namespace BstLean.Part269.N13050
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13050)
open BstLean.Part268 (cell13050)

noncomputable def sourceNumerics13050 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13050 (cell13050 i)
      scalarRow13050.M scalarRow13050.H scalarRow13050.xi := by
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
    energy_allowance := scalarRow13050.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13050]
    centre_nonneg := (scalarRow13050.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D28.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13050])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13050
/-! Actual 13051 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13051
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13051 ≤ (1.035320197192 : ℝ) := by
  have hr : (114.240973385208 : ℝ) ≤ √(13051 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.240973385208 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13051 13051 (11 / 1000) ≤
    (0.008367286289 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13051) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.240973385208 : ℝ) ≤ √(13051 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13051)
  have hdiv : K / √(13051 : ℝ) ≤ K / 114.240973385208 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.240973385208 ≤ (0.008367286289 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13051.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13051 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13051 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13051 := gPlus_lower 13051
end BstLean.Part269.N13051

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13051
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035320197191 : ℝ) ≤ wn 13051 := by
  have hn : √(13051 : ℝ) ≤ 114.240973385209 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13051 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.240973385209 ≤ 2 / √(13051 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000244990942 : ℝ) ≤ rhoBar 13051 BstLean.Part154.csC ∧
    rhoBar 13051 BstLean.Part154.csC ≤ 0.000244991321 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035320197191 : ℝ) / (1.295212 * 13051) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035320197192 : ℝ) / (1.29521 * 13051) := by gcongr
      _ ≤ (0.000244991321 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13051 BstLean.Part154.csC) ≤ 0.000980025305 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13051 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13051 BstLean.Part154.csC) (piBar (rhoBar 13051 BstLean.Part154.csC)) ≤ 0.000187125786 ∧
    cc1 (rhoBar 13051 BstLean.Part154.csC) (piBar (rhoBar 13051 BstLean.Part154.csC)) ≤ 0.000119069429 ∧
    cc2 (rhoBar 13051 BstLean.Part154.csC) ≤ 0.000069120775 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13051 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13051 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13051 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13051 BstLean.Part154.csC * nuR (rhoBar 13051 BstLean.Part154.csC)) ≤ 0.000489997648 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000244991321 : ℝ) * 0.000980025305 := by gcongr
      _ ≤ (0.000489997648 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13051 BstLean.Part154.csC) * nuR (rhoBar 13051 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000980025305 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13051 BstLean.Part154.csC) * rhoBar 13051 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000244991321 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000244991321 / 2 + 0.399 * 0.000980025305 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000187125786 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000489997648 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119069429 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000244991321 / 1.414213562 := by gcongr
      _ ≤ (0.000069120775 : ℝ) := by norm_num

end BstLean.Part269.N13051

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13051
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13051 BstLean.Part154.csC) (piBar (rhoBar 13051 BstLean.Part154.csC)) ≤ 1.51218E-7 := by
  have hr0 : 0 ≤ rhoBar 13051 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13051 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13051 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13051 BstLean.Part154.csC) (piBar (rhoBar 13051 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13051 BstLean.Part154.csC) (piBar (rhoBar 13051 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13051 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000187125786 : ℝ) ^ 2 + 0.000119069429 ^ 2 + 3 * 0.000069120775 ^ 2 +
        2 * 0.797885 * 0.000187125786 * 0.000119069429 + 2 * 0.000187125786 * 0.000069120775 +
        4 * 0.797885 * 0.000119069429 * 0.000069120775 := by gcongr
    _ ≤ (1.51218E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13051 BstLean.Part154.csC Θ ≤ 0.002556160621 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13051 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13051 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13051 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13051 BstLean.Part154.csC) (piBar (rhoBar 13051 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13051 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035320197192 * 1.51218E-7 / (0.000244990942 : ℝ) := by gcongr
    _ ≤ 0.002556160621 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13051 BstLean.Part154.csC Θ ≤ 0.002834853845 + 0.000645900455 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13051 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13051 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13051 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035320197192 : ℝ) * ((2 * Θ * 0.000244991321 +
        (6863 / 10000) * 0.000244991321 * 13051 * 0.000980025305) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002834853845 + 0.000645900455 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13051 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13051 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13051 0.011 Θ ∧ gammaRatio 13051 0.011 Θ ≤ 0.000084221681 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13051 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035320197192 : ℝ) * 0.525 / ((1 - 0.011) * 13051) := by gcongr
      _ ≤ (0.000084221681 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13051 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13051 0.011 Θ) :=
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
    badAllowance 13051 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000383749387 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13051 BstLean.Part154.csC) 1.22 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 2 (rhoBar 13051 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13051 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13051 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13051 0.011 Θ) 1.12 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 1 (gammaRatio 13051 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13051 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13051 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13051 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13051 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035320197192 : ℝ) * 13051 *
        (1.3781E-8 / 1.1045361 + 1.6832E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000383749387 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13051 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003218603232 + 0.003202061076 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13051

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13051
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13051 BstLean.Part154.csC) (piBar (rhoBar 13051 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13051 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13051 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13051 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13051 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13051 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13051 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13051 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13051 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13051 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13051 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13051 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13051 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13051 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13051 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051766132303 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13051) ≤ 0.010453671268 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13051 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035320197192)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010453671268 + 2 * 0.737676 / 13051) := by gcongr
    _ ≤ (0.051766132303 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13051 12 ≤ 0.0015 := by
  exact BstLean.Part269.S28.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13051

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13051
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560519014650 : ℝ) ≤ plow 13051 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13051) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052406285297)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001341984327) : eMP 13051 0.011 xi bn ≤ 0.001155788029 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13051 : ℝ) * (1 - 0.011))) ≤ 0.000571516327 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001341984327 / (13051 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000571516327 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000571516327 : ℝ) + 3.141593 * 0.052406285297 / (13051 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001155788029 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052406285297)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001341984327) : PiBarMP 13051 12 0.011 xi bn ≤ 0.159046396199 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13051 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036633104251 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.610910567603 : ℝ) ≤ √((13051 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.240973385208 : ℝ) ≤ √(13051 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13051) ≤ 0.121956316109 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036633104251 + 0.052406285297 * 1.772454 / (2 * (113.610910567603 : ℝ))) * (1 + 0.001155788029) +
        8 / (13051 * 114.240973385208) + 0.121956316109 := by gcongr
    _ ≤ (0.159046396199 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052406285297)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001341984327) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280690323461) :
    parallelOracle 13051 0.011 xi bn cd ≤ 0.160010176251 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13051 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13051 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560519014650 : ℝ) ≤ plow 13051 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.240973385208 : ℝ) ≤ √(13051 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280690323461 : ℝ) / (2 * 0.560519014650 * 114.240973385208)) * 0.159046396199 +
        0.280690323461 ^ 2 / (2 * 0.560519014650 * 114.240973385208) := by gcongr
    _ ≤ (0.160010176251 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052406285297) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001341984327)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280690323461) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13051 13051 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560519014650 : ℝ) ≤ plow 13051 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.240973385208 : ℝ) ≤ √(13051 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13051 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13051 Θ 1.22 ≤ 0.011607923679 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.240973385208 := by gcongr <;> linarith
      _ ≤ (0.011607923679 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13051 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13051 13051 0.011 ≤ 0.008367286289 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13051 13051 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13051 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13051 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13051 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13051 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160010176251 + 0.011607923679 + (0.008367286289 : ℝ) *
        (1 + 2 * (0.280690323461 + 0.011607923679) / (0.560519014650 * 114.240973385208))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13051]

end BstLean.Part269.N13051

/-! The original eight local profiles supply actual 13051 moment certificates. -/
namespace BstLean.Part269.N13051
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13051 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13051 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13051 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052406285297 ∧
    0 ≤ bN 13051 BstLean.Part154.csC (groupTheta g) ∧ bN 13051 BstLean.Part154.csC (groupTheta g) ≤ 0.001341984327 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13051 13051 0.011
      (momentAllowance 13051 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13051 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13051 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13051 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13051 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13051 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228924191158 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13051 0.011
      (momentAllowance 13051 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13051 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13051
/-! The actual computed-centre upper energy formula at 13051. -/
namespace BstLean.Part269.N13051
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13051

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13051
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13051)
open BstLean.Part268 (cell13051)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084527599494
  | 2 => 0.085454546477
  | 3 => 0.086377442998
  | 4 => 0.087297192432
  | 5 => 0.088214902417
  | 6 => 0.089131917035
  | 7 => 0.090049852375
  | 8 => 0.090970635582
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13051 13051 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13051 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003218831707 + 0.003202305177 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S28.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13051

/-! Actual upper energy certificates on all 43 source endpoints at 13051. -/
namespace BstLean.Part269.N13051
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13051)
open BstLean.Part268 (cell13051)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13051 (gMinus 13051) (1 - (cell13051 i).lower) ≤ 1 ∧
    energyUpper 13051 (gMinus 13051) (BstLean.Part211.gPlus 13051)
      (finiteEnergy 13051 13051 0.011) (1 - (cell13051 i).lower) ≤
      (cell13051 i).energy := by
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
      have E := BstLean.Part269.S28.uniformEnergy10 (n := 13051) (by norm_num)
        (q := 1 - (cell13051 ⟨10,by decide⟩).lower)
        (by norm_num [cell13051]) (by norm_num [cell13051])
      exact ⟨E.1,E.2.trans (by norm_num [cell13051])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy11 (n := 13051) (by norm_num)
        (q := 1 - (cell13051 ⟨11,by decide⟩).lower)
        (by norm_num [cell13051]) (by norm_num [cell13051])
      exact ⟨E.1,E.2.trans (by norm_num [cell13051])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy12 (n := 13051) (by norm_num)
        (q := 1 - (cell13051 ⟨12,by decide⟩).lower)
        (by norm_num [cell13051]) (by norm_num [cell13051])
      exact ⟨E.1,E.2.trans (by norm_num [cell13051])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy13 (n := 13051) (by norm_num)
        (q := 1 - (cell13051 ⟨13,by decide⟩).lower)
        (by norm_num [cell13051]) (by norm_num [cell13051])
      exact ⟨E.1,E.2.trans (by norm_num [cell13051])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy14 (n := 13051) (by norm_num)
        (q := 1 - (cell13051 ⟨14,by decide⟩).lower)
        (by norm_num [cell13051]) (by norm_num [cell13051])
      exact ⟨E.1,E.2.trans (by norm_num [cell13051])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy15 (n := 13051) (by norm_num)
        (q := 1 - (cell13051 ⟨15,by decide⟩).lower)
        (by norm_num [cell13051]) (by norm_num [cell13051])
      exact ⟨E.1,E.2.trans (by norm_num [cell13051])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy16 (n := 13051) (by norm_num)
        (q := 1 - (cell13051 ⟨16,by decide⟩).lower)
        (by norm_num [cell13051]) (by norm_num [cell13051])
      exact ⟨E.1,E.2.trans (by norm_num [cell13051])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy17 (n := 13051) (by norm_num)
        (q := 1 - (cell13051 ⟨17,by decide⟩).lower)
        (by norm_num [cell13051]) (by norm_num [cell13051])
      exact ⟨E.1,E.2.trans (by norm_num [cell13051])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy18 (n := 13051) (by norm_num)
        (q := 1 - (cell13051 ⟨18,by decide⟩).lower)
        (by norm_num [cell13051]) (by norm_num [cell13051])
      exact ⟨E.1,E.2.trans (by norm_num [cell13051])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy19 (n := 13051) (by norm_num)
        (q := 1 - (cell13051 ⟨19,by decide⟩).lower)
        (by norm_num [cell13051]) (by norm_num [cell13051])
      exact ⟨E.1,E.2.trans (by norm_num [cell13051])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy20 (n := 13051) (by norm_num)
        (q := 1 - (cell13051 ⟨20,by decide⟩).lower)
        (by norm_num [cell13051]) (by norm_num [cell13051])
      exact ⟨E.1,E.2.trans (by norm_num [cell13051])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy21 (n := 13051) (by norm_num)
        (q := 1 - (cell13051 ⟨21,by decide⟩).lower)
        (by norm_num [cell13051]) (by norm_num [cell13051])
      exact ⟨E.1,E.2.trans (by norm_num [cell13051])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy22 (n := 13051) (by norm_num)
        (q := 1 - (cell13051 ⟨22,by decide⟩).lower)
        (by norm_num [cell13051]) (by norm_num [cell13051])
      exact ⟨E.1,E.2.trans (by norm_num [cell13051])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy23 (n := 13051) (by norm_num)
        (q := 1 - (cell13051 ⟨23,by decide⟩).lower)
        (by norm_num [cell13051]) (by norm_num [cell13051])
      exact ⟨E.1,E.2.trans (by norm_num [cell13051])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy24 (n := 13051) (by norm_num)
        (q := 1 - (cell13051 ⟨24,by decide⟩).lower)
        (by norm_num [cell13051]) (by norm_num [cell13051])
      exact ⟨E.1,E.2.trans (by norm_num [cell13051])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy25 (n := 13051) (by norm_num)
        (q := 1 - (cell13051 ⟨25,by decide⟩).lower)
        (by norm_num [cell13051]) (by norm_num [cell13051])
      exact ⟨E.1,E.2.trans (by norm_num [cell13051])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy26 (n := 13051) (by norm_num)
        (q := 1 - (cell13051 ⟨26,by decide⟩).lower)
        (by norm_num [cell13051]) (by norm_num [cell13051])
      exact ⟨E.1,E.2.trans (by norm_num [cell13051])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy27 (n := 13051) (by norm_num)
        (q := 1 - (cell13051 ⟨27,by decide⟩).lower)
        (by norm_num [cell13051]) (by norm_num [cell13051])
      exact ⟨E.1,E.2.trans (by norm_num [cell13051])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy28 (n := 13051) (by norm_num)
        (q := 1 - (cell13051 ⟨28,by decide⟩).lower)
        (by norm_num [cell13051]) (by norm_num [cell13051])
      exact ⟨E.1,E.2.trans (by norm_num [cell13051])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy29 (n := 13051) (by norm_num)
        (q := 1 - (cell13051 ⟨29,by decide⟩).lower)
        (by norm_num [cell13051]) (by norm_num [cell13051])
      exact ⟨E.1,E.2.trans (by norm_num [cell13051])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy30 (n := 13051) (by norm_num)
        (q := 1 - (cell13051 ⟨30,by decide⟩).lower)
        (by norm_num [cell13051]) (by norm_num [cell13051])
      exact ⟨E.1,E.2.trans (by norm_num [cell13051])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy31 (n := 13051) (by norm_num)
        (q := 1 - (cell13051 ⟨31,by decide⟩).lower)
        (by norm_num [cell13051]) (by norm_num [cell13051])
      exact ⟨E.1,E.2.trans (by norm_num [cell13051])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy32 (n := 13051) (by norm_num)
        (q := 1 - (cell13051 ⟨32,by decide⟩).lower)
        (by norm_num [cell13051]) (by norm_num [cell13051])
      exact ⟨E.1,E.2.trans (by norm_num [cell13051])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy33 (n := 13051) (by norm_num)
        (q := 1 - (cell13051 ⟨33,by decide⟩).lower)
        (by norm_num [cell13051]) (by norm_num [cell13051])
      exact ⟨E.1,E.2.trans (by norm_num [cell13051])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy34 (n := 13051) (by norm_num)
        (q := 1 - (cell13051 ⟨34,by decide⟩).lower)
        (by norm_num [cell13051]) (by norm_num [cell13051])
      exact ⟨E.1,E.2.trans (by norm_num [cell13051])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy35 (n := 13051) (by norm_num)
        (q := 1 - (cell13051 ⟨35,by decide⟩).lower)
        (by norm_num [cell13051]) (by norm_num [cell13051])
      exact ⟨E.1,E.2.trans (by norm_num [cell13051])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy36 (n := 13051) (by norm_num)
        (q := 1 - (cell13051 ⟨36,by decide⟩).lower)
        (by norm_num [cell13051]) (by norm_num [cell13051])
      exact ⟨E.1,E.2.trans (by norm_num [cell13051])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy37 (n := 13051) (by norm_num)
        (q := 1 - (cell13051 ⟨37,by decide⟩).lower)
        (by norm_num [cell13051]) (by norm_num [cell13051])
      exact ⟨E.1,E.2.trans (by norm_num [cell13051])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy38 (n := 13051) (by norm_num)
        (q := 1 - (cell13051 ⟨38,by decide⟩).lower)
        (by norm_num [cell13051]) (by norm_num [cell13051])
      exact ⟨E.1,E.2.trans (by norm_num [cell13051])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy39 (n := 13051) (by norm_num)
        (q := 1 - (cell13051 ⟨39,by decide⟩).lower)
        (by norm_num [cell13051]) (by norm_num [cell13051])
      exact ⟨E.1,E.2.trans (by norm_num [cell13051])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy40 (n := 13051) (by norm_num)
        (q := 1 - (cell13051 ⟨40,by decide⟩).lower)
        (by norm_num [cell13051]) (by norm_num [cell13051])
      exact ⟨E.1,E.2.trans (by norm_num [cell13051])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy41 (n := 13051) (by norm_num)
        (q := 1 - (cell13051 ⟨41,by decide⟩).lower)
        (by norm_num [cell13051]) (by norm_num [cell13051])
      exact ⟨E.1,E.2.trans (by norm_num [cell13051])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy42 (n := 13051) (by norm_num)
        (q := 1 - (cell13051 ⟨42,by decide⟩).lower)
        (by norm_num [cell13051]) (by norm_num [cell13051])
      exact ⟨E.1,E.2.trans (by norm_num [cell13051])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy43 (n := 13051) (by norm_num)
        (q := 1 - (cell13051 ⟨43,by decide⟩).lower)
        (by norm_num [cell13051]) (by norm_num [cell13051])
      exact ⟨E.1,E.2.trans (by norm_num [cell13051])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy44 (n := 13051) (by norm_num)
        (q := 1 - (cell13051 ⟨44,by decide⟩).lower)
        (by norm_num [cell13051]) (by norm_num [cell13051])
      exact ⟨E.1,E.2.trans (by norm_num [cell13051])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy45 (n := 13051) (by norm_num)
        (q := 1 - (cell13051 ⟨45,by decide⟩).lower)
        (by norm_num [cell13051]) (by norm_num [cell13051])
      exact ⟨E.1,E.2.trans (by norm_num [cell13051])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy46 (n := 13051) (by norm_num)
        (q := 1 - (cell13051 ⟨46,by decide⟩).lower)
        (by norm_num [cell13051]) (by norm_num [cell13051])
      exact ⟨E.1,E.2.trans (by norm_num [cell13051])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy47 (n := 13051) (by norm_num)
        (q := 1 - (cell13051 ⟨47,by decide⟩).lower)
        (by norm_num [cell13051]) (by norm_num [cell13051])
      exact ⟨E.1,E.2.trans (by norm_num [cell13051])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy48 (n := 13051) (by norm_num)
        (q := 1 - (cell13051 ⟨48,by decide⟩).lower)
        (by norm_num [cell13051]) (by norm_num [cell13051])
      exact ⟨E.1,E.2.trans (by norm_num [cell13051])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy49 (n := 13051) (by norm_num)
        (q := 1 - (cell13051 ⟨49,by decide⟩).lower)
        (by norm_num [cell13051]) (by norm_num [cell13051])
      exact ⟨E.1,E.2.trans (by norm_num [cell13051])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy50 (n := 13051) (by norm_num)
        (q := 1 - (cell13051 ⟨50,by decide⟩).lower)
        (by norm_num [cell13051]) (by norm_num [cell13051])
      exact ⟨E.1,E.2.trans (by norm_num [cell13051])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy51 (n := 13051) (by norm_num)
        (q := 1 - (cell13051 ⟨51,by decide⟩).lower)
        (by norm_num [cell13051]) (by norm_num [cell13051])
      exact ⟨E.1,E.2.trans (by norm_num [cell13051])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy52 (n := 13051) (by norm_num)
        (q := 1 - (cell13051 ⟨52,by decide⟩).lower)
        (by norm_num [cell13051]) (by norm_num [cell13051])
      exact ⟨E.1,E.2.trans (by norm_num [cell13051])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13051

/-! Source-cell containment and simple scalar guards at 13051. -/
namespace BstLean.Part269.N13051
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13051)
open BstLean.Part268 (cell13051)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13051 ⟨10,by decide⟩).lower ∧ (cell13051 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13051 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13051 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13051 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13051 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13051 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13051,cell13051,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13051 ⟨11,by decide⟩).lower ∧ (cell13051 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13051 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13051 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13051 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13051 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13051 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13051,cell13051,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13051 ⟨12,by decide⟩).lower ∧ (cell13051 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13051 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13051 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13051 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13051 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13051 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13051,cell13051,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13051 ⟨13,by decide⟩).lower ∧ (cell13051 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13051 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13051 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13051 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13051 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13051 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13051,cell13051,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13051 ⟨14,by decide⟩).lower ∧ (cell13051 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13051 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13051 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13051 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13051 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13051 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13051,cell13051,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13051 ⟨15,by decide⟩).lower ∧ (cell13051 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13051 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13051 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13051 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13051 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13051 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13051,cell13051,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13051 ⟨16,by decide⟩).lower ∧ (cell13051 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13051 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13051 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13051 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13051 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13051 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13051,cell13051,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13051 ⟨17,by decide⟩).lower ∧ (cell13051 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13051 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13051 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13051 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13051 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13051 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13051,cell13051,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13051 ⟨18,by decide⟩).lower ∧ (cell13051 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13051 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13051 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13051 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13051 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13051 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13051,cell13051,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13051 ⟨19,by decide⟩).lower ∧ (cell13051 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13051 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13051 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13051 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13051 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13051 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13051,cell13051,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13051 ⟨20,by decide⟩).lower ∧ (cell13051 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13051 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13051 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13051 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13051 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13051 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13051,cell13051,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13051 ⟨21,by decide⟩).lower ∧ (cell13051 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13051 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13051 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13051 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13051 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13051 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13051,cell13051,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13051 ⟨22,by decide⟩).lower ∧ (cell13051 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13051 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13051 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13051 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13051 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13051 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13051,cell13051,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13051 ⟨23,by decide⟩).lower ∧ (cell13051 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13051 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13051 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13051 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13051 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13051 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13051,cell13051,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13051 ⟨24,by decide⟩).lower ∧ (cell13051 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13051 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13051 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13051 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13051 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13051 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13051,cell13051,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13051 ⟨25,by decide⟩).lower ∧ (cell13051 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13051 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13051 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13051 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13051 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13051 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13051,cell13051,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13051 ⟨26,by decide⟩).lower ∧ (cell13051 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13051 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13051 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13051 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13051 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13051 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13051,cell13051,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13051 ⟨27,by decide⟩).lower ∧ (cell13051 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13051 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13051 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13051 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13051 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13051 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13051,cell13051,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13051 ⟨28,by decide⟩).lower ∧ (cell13051 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13051 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13051 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13051 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13051 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13051 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13051,cell13051,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13051 ⟨29,by decide⟩).lower ∧ (cell13051 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13051 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13051 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13051 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13051 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13051 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13051,cell13051,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13051 ⟨30,by decide⟩).lower ∧ (cell13051 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13051 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13051 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13051 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13051 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13051 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13051,cell13051,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13051 ⟨31,by decide⟩).lower ∧ (cell13051 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13051 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13051 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13051 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13051 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13051 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13051,cell13051,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13051 ⟨32,by decide⟩).lower ∧ (cell13051 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13051 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13051 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13051 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13051 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13051 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13051,cell13051,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13051 ⟨33,by decide⟩).lower ∧ (cell13051 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13051 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13051 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13051 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13051 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13051 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13051,cell13051,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13051 ⟨34,by decide⟩).lower ∧ (cell13051 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13051 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13051 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13051 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13051 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13051 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13051,cell13051,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13051 ⟨35,by decide⟩).lower ∧ (cell13051 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13051 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13051 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13051 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13051 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13051 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13051,cell13051,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13051 ⟨36,by decide⟩).lower ∧ (cell13051 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13051 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13051 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13051 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13051 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13051 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13051,cell13051,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13051 ⟨37,by decide⟩).lower ∧ (cell13051 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13051 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13051 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13051 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13051 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13051 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13051,cell13051,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13051 ⟨38,by decide⟩).lower ∧ (cell13051 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13051 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13051 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13051 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13051 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13051 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13051,cell13051,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13051 ⟨39,by decide⟩).lower ∧ (cell13051 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13051 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13051 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13051 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13051 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13051 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13051,cell13051,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13051 ⟨40,by decide⟩).lower ∧ (cell13051 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13051 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13051 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13051 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13051 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13051 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13051,cell13051,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13051 ⟨41,by decide⟩).lower ∧ (cell13051 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13051 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13051 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13051 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13051 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13051 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13051,cell13051,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13051 ⟨42,by decide⟩).lower ∧ (cell13051 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13051 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13051 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13051 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13051 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13051 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13051,cell13051,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13051 ⟨43,by decide⟩).lower ∧ (cell13051 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13051 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13051 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13051 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13051 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13051 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13051,cell13051,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13051 ⟨44,by decide⟩).lower ∧ (cell13051 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13051 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13051 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13051 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13051 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13051 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13051,cell13051,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13051 ⟨45,by decide⟩).lower ∧ (cell13051 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13051 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13051 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13051 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13051 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13051 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13051,cell13051,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13051 ⟨46,by decide⟩).lower ∧ (cell13051 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13051 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13051 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13051 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13051 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13051 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13051,cell13051,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13051 ⟨47,by decide⟩).lower ∧ (cell13051 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13051 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13051 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13051 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13051 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13051 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13051,cell13051,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13051 ⟨48,by decide⟩).lower ∧ (cell13051 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13051 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13051 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13051 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13051 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13051 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13051,cell13051,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13051 ⟨49,by decide⟩).lower ∧ (cell13051 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13051 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13051 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13051 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13051 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13051 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13051,cell13051,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13051 ⟨50,by decide⟩).lower ∧ (cell13051 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13051 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13051 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13051 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13051 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13051 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13051,cell13051,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13051 ⟨51,by decide⟩).lower ∧ (cell13051 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13051 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13051 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13051 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13051 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13051 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13051,cell13051,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13051 ⟨52,by decide⟩).lower ∧ (cell13051 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13051 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13051 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13051 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13051 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13051 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13051,cell13051,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13051 i).lower ∧
    (cell13051 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13051 i).upper ≤ (0.532 : ℝ) ∧
    (cell13051 i).centre ≤ (0.1 : ℝ) ∧ (cell13051 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13051 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13051 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13051

/-! The local source numeric instances at 13051 have no network premises. -/
namespace BstLean.Part269.N13051
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13051)
open BstLean.Part268 (cell13051)

noncomputable def sourceNumerics13051 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13051 (cell13051 i)
      scalarRow13051.M scalarRow13051.H scalarRow13051.xi := by
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
    energy_allowance := scalarRow13051.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13051]
    centre_nonneg := (scalarRow13051.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D28.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13051])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13051
/-! Actual 13052 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13052
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13052 ≤ (1.035318832368 : ℝ) := by
  have hr : (114.245350014781 : ℝ) ≤ √(13052 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.245350014781 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13052 13052 (11 / 1000) ≤
    (0.008366965744 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13052) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.245350014781 : ℝ) ≤ √(13052 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13052)
  have hdiv : K / √(13052 : ℝ) ≤ K / 114.245350014781 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.245350014781 ≤ (0.008366965744 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13052.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13052 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13052 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13052 := gPlus_lower 13052
end BstLean.Part269.N13052

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13052
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035318832367 : ℝ) ≤ wn 13052 := by
  have hn : √(13052 : ℝ) ≤ 114.245350014782 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13052 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.245350014782 ≤ 2 / √(13052 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000244971849 : ℝ) ≤ rhoBar 13052 BstLean.Part154.csC ∧
    rhoBar 13052 BstLean.Part154.csC ≤ 0.000244972228 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035318832367 : ℝ) / (1.295212 * 13052) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035318832368 : ℝ) / (1.29521 * 13052) := by gcongr
      _ ≤ (0.000244972228 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13052 BstLean.Part154.csC) ≤ 0.000979948924 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13052 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13052 BstLean.Part154.csC) (piBar (rhoBar 13052 BstLean.Part154.csC)) ≤ 0.000187111202 ∧
    cc1 (rhoBar 13052 BstLean.Part154.csC) (piBar (rhoBar 13052 BstLean.Part154.csC)) ≤ 0.000119060149 ∧
    cc2 (rhoBar 13052 BstLean.Part154.csC) ≤ 0.000069115388 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13052 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13052 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13052 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13052 BstLean.Part154.csC * nuR (rhoBar 13052 BstLean.Part154.csC)) ≤ 0.000489959459 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000244972228 : ℝ) * 0.000979948924 := by gcongr
      _ ≤ (0.000489959459 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13052 BstLean.Part154.csC) * nuR (rhoBar 13052 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000979948924 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13052 BstLean.Part154.csC) * rhoBar 13052 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000244972228 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000244972228 / 2 + 0.399 * 0.000979948924 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000187111202 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000489959459 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119060149 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000244972228 / 1.414213562 := by gcongr
      _ ≤ (0.000069115388 : ℝ) := by norm_num

end BstLean.Part269.N13052

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13052
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13052 BstLean.Part154.csC) (piBar (rhoBar 13052 BstLean.Part154.csC)) ≤ 1.51194E-7 := by
  have hr0 : 0 ≤ rhoBar 13052 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13052 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13052 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13052 BstLean.Part154.csC) (piBar (rhoBar 13052 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13052 BstLean.Part154.csC) (piBar (rhoBar 13052 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13052 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000187111202 : ℝ) ^ 2 + 0.000119060149 ^ 2 + 3 * 0.000069115388 ^ 2 +
        2 * 0.797885 * 0.000187111202 * 0.000119060149 + 2 * 0.000187111202 * 0.000069115388 +
        4 * 0.797885 * 0.000119060149 * 0.000069115388 := by gcongr
    _ ≤ (1.51194E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13052 BstLean.Part154.csC Θ ≤ 0.002555950755 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13052 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13052 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13052 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13052 BstLean.Part154.csC) (piBar (rhoBar 13052 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13052 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035318832368 * 1.51194E-7 / (0.000244971849 : ℝ) := by gcongr
    _ ≤ 0.002555950755 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13052 BstLean.Part154.csC Θ ≤ 0.002834625433 + 0.000645849267 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13052 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13052 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13052 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035318832368 : ℝ) * ((2 * Θ * 0.000244972228 +
        (6863 / 10000) * 0.000244972228 * 13052 * 0.000979948924) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002834625433 + 0.000645849267 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13052 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13052 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13052 0.011 Θ ∧ gammaRatio 13052 0.011 Θ ≤ 0.000084215117 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13052 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035318832368 : ℝ) * 0.525 / ((1 - 0.011) * 13052) := by gcongr
      _ ≤ (0.000084215117 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13052 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13052 0.011 Θ) :=
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
    badAllowance 13052 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000383749387 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13052 BstLean.Part154.csC) 1.22 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 2 (rhoBar 13052 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13052 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13052 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13052 0.011 Θ) 1.12 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 1 (gammaRatio 13052 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13052 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13052 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13052 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13052 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035318832368 : ℝ) * 13052 *
        (1.3781E-8 / 1.1045361 + 1.6832E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000383749387 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13052 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003218374820 + 0.003201800022 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13052

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13052
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13052 BstLean.Part154.csC) (piBar (rhoBar 13052 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13052 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13052 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13052 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13052 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13052 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13052 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13052 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13052 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13052 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13052 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13052 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13052 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13052 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13052 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051764127978 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13052) ≤ 0.010453270798 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13052 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035318832368)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010453270798 + 2 * 0.737676 / 13052) := by gcongr
    _ ≤ (0.051764127978 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13052 12 ≤ 0.0015 := by
  exact BstLean.Part269.S28.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13052

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13052
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560519057470 : ℝ) ≤ plow 13052 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13052) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052405919832)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001341874147) : eMP 13052 0.011 xi bn ≤ 0.001155696253 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13052 : ℝ) * (1 - 0.011))) ≤ 0.000571470972 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001341874147 / (13052 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000571470972 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000571470972 : ℝ) + 3.141593 * 0.052405919832 / (13052 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001155696253 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052405919832)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001341874147) : PiBarMP 13052 12 0.011 xi bn ≤ 0.159040196021 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13052 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036631600389 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.615263059150 : ℝ) ≤ √((13052 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.245350014781 : ℝ) ≤ √(13052 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13052) ≤ 0.121951644080 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036631600389 + 0.052405919832 * 1.772454 / (2 * (113.615263059150 : ℝ))) * (1 + 0.001155696253) +
        8 / (13052 * 114.245350014781) + 0.121951644080 := by gcongr
    _ ≤ (0.159040196021 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052405919832)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001341874147) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280687520912) :
    parallelOracle 13052 0.011 xi bn cd ≤ 0.160003909725 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13052 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13052 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560519057470 : ℝ) ≤ plow 13052 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.245350014781 : ℝ) ≤ √(13052 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280687520912 : ℝ) / (2 * 0.560519057470 * 114.245350014781)) * 0.159040196021 +
        0.280687520912 ^ 2 / (2 * 0.560519057470 * 114.245350014781) := by gcongr
    _ ≤ (0.160003909725 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052405919832) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001341874147)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280687520912) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13052 13052 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560519057470 : ℝ) ≤ plow 13052 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.245350014781 : ℝ) ≤ √(13052 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13052 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13052 Θ 1.22 ≤ 0.011607478990 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.245350014781 := by gcongr <;> linarith
      _ ≤ (0.011607478990 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13052 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13052 13052 0.011 ≤ 0.008366965744 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13052 13052 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13052 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13052 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13052 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13052 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160003909725 + 0.011607478990 + (0.008366965744 : ℝ) *
        (1 + 2 * (0.280687520912 + 0.011607478990) / (0.560519057470 * 114.245350014781))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13052]

end BstLean.Part269.N13052

/-! The original eight local profiles supply actual 13052 moment certificates. -/
namespace BstLean.Part269.N13052
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13052 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13052 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13052 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052405919832 ∧
    0 ≤ bN 13052 BstLean.Part154.csC (groupTheta g) ∧ bN 13052 BstLean.Part154.csC (groupTheta g) ≤ 0.001341874147 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13052 13052 0.011
      (momentAllowance 13052 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13052 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13052 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13052 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13052 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13052 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228923392934 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13052 0.011
      (momentAllowance 13052 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13052 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13052
/-! The actual computed-centre upper energy formula at 13052. -/
namespace BstLean.Part269.N13052
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13052

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13052
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13052)
open BstLean.Part268 (cell13052)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084525021501
  | 2 => 0.085451935344
  | 3 => 0.086374793807
  | 4 => 0.087294499108
  | 5 => 0.088212157509
  | 6 => 0.089129111479
  | 7 => 0.090046975220
  | 8 => 0.090967673688
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13052 13052 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13052 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003218831707 + 0.003202305177 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S28.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13052

/-! Actual upper energy certificates on all 43 source endpoints at 13052. -/
namespace BstLean.Part269.N13052
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13052)
open BstLean.Part268 (cell13052)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13052 (gMinus 13052) (1 - (cell13052 i).lower) ≤ 1 ∧
    energyUpper 13052 (gMinus 13052) (BstLean.Part211.gPlus 13052)
      (finiteEnergy 13052 13052 0.011) (1 - (cell13052 i).lower) ≤
      (cell13052 i).energy := by
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
      have E := BstLean.Part269.S28.uniformEnergy10 (n := 13052) (by norm_num)
        (q := 1 - (cell13052 ⟨10,by decide⟩).lower)
        (by norm_num [cell13052]) (by norm_num [cell13052])
      exact ⟨E.1,E.2.trans (by norm_num [cell13052])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy11 (n := 13052) (by norm_num)
        (q := 1 - (cell13052 ⟨11,by decide⟩).lower)
        (by norm_num [cell13052]) (by norm_num [cell13052])
      exact ⟨E.1,E.2.trans (by norm_num [cell13052])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy12 (n := 13052) (by norm_num)
        (q := 1 - (cell13052 ⟨12,by decide⟩).lower)
        (by norm_num [cell13052]) (by norm_num [cell13052])
      exact ⟨E.1,E.2.trans (by norm_num [cell13052])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy13 (n := 13052) (by norm_num)
        (q := 1 - (cell13052 ⟨13,by decide⟩).lower)
        (by norm_num [cell13052]) (by norm_num [cell13052])
      exact ⟨E.1,E.2.trans (by norm_num [cell13052])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy14 (n := 13052) (by norm_num)
        (q := 1 - (cell13052 ⟨14,by decide⟩).lower)
        (by norm_num [cell13052]) (by norm_num [cell13052])
      exact ⟨E.1,E.2.trans (by norm_num [cell13052])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy15 (n := 13052) (by norm_num)
        (q := 1 - (cell13052 ⟨15,by decide⟩).lower)
        (by norm_num [cell13052]) (by norm_num [cell13052])
      exact ⟨E.1,E.2.trans (by norm_num [cell13052])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy16 (n := 13052) (by norm_num)
        (q := 1 - (cell13052 ⟨16,by decide⟩).lower)
        (by norm_num [cell13052]) (by norm_num [cell13052])
      exact ⟨E.1,E.2.trans (by norm_num [cell13052])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy17 (n := 13052) (by norm_num)
        (q := 1 - (cell13052 ⟨17,by decide⟩).lower)
        (by norm_num [cell13052]) (by norm_num [cell13052])
      exact ⟨E.1,E.2.trans (by norm_num [cell13052])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy18 (n := 13052) (by norm_num)
        (q := 1 - (cell13052 ⟨18,by decide⟩).lower)
        (by norm_num [cell13052]) (by norm_num [cell13052])
      exact ⟨E.1,E.2.trans (by norm_num [cell13052])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy19 (n := 13052) (by norm_num)
        (q := 1 - (cell13052 ⟨19,by decide⟩).lower)
        (by norm_num [cell13052]) (by norm_num [cell13052])
      exact ⟨E.1,E.2.trans (by norm_num [cell13052])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy20 (n := 13052) (by norm_num)
        (q := 1 - (cell13052 ⟨20,by decide⟩).lower)
        (by norm_num [cell13052]) (by norm_num [cell13052])
      exact ⟨E.1,E.2.trans (by norm_num [cell13052])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy21 (n := 13052) (by norm_num)
        (q := 1 - (cell13052 ⟨21,by decide⟩).lower)
        (by norm_num [cell13052]) (by norm_num [cell13052])
      exact ⟨E.1,E.2.trans (by norm_num [cell13052])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy22 (n := 13052) (by norm_num)
        (q := 1 - (cell13052 ⟨22,by decide⟩).lower)
        (by norm_num [cell13052]) (by norm_num [cell13052])
      exact ⟨E.1,E.2.trans (by norm_num [cell13052])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy23 (n := 13052) (by norm_num)
        (q := 1 - (cell13052 ⟨23,by decide⟩).lower)
        (by norm_num [cell13052]) (by norm_num [cell13052])
      exact ⟨E.1,E.2.trans (by norm_num [cell13052])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy24 (n := 13052) (by norm_num)
        (q := 1 - (cell13052 ⟨24,by decide⟩).lower)
        (by norm_num [cell13052]) (by norm_num [cell13052])
      exact ⟨E.1,E.2.trans (by norm_num [cell13052])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy25 (n := 13052) (by norm_num)
        (q := 1 - (cell13052 ⟨25,by decide⟩).lower)
        (by norm_num [cell13052]) (by norm_num [cell13052])
      exact ⟨E.1,E.2.trans (by norm_num [cell13052])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy26 (n := 13052) (by norm_num)
        (q := 1 - (cell13052 ⟨26,by decide⟩).lower)
        (by norm_num [cell13052]) (by norm_num [cell13052])
      exact ⟨E.1,E.2.trans (by norm_num [cell13052])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy27 (n := 13052) (by norm_num)
        (q := 1 - (cell13052 ⟨27,by decide⟩).lower)
        (by norm_num [cell13052]) (by norm_num [cell13052])
      exact ⟨E.1,E.2.trans (by norm_num [cell13052])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy28 (n := 13052) (by norm_num)
        (q := 1 - (cell13052 ⟨28,by decide⟩).lower)
        (by norm_num [cell13052]) (by norm_num [cell13052])
      exact ⟨E.1,E.2.trans (by norm_num [cell13052])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy29 (n := 13052) (by norm_num)
        (q := 1 - (cell13052 ⟨29,by decide⟩).lower)
        (by norm_num [cell13052]) (by norm_num [cell13052])
      exact ⟨E.1,E.2.trans (by norm_num [cell13052])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy30 (n := 13052) (by norm_num)
        (q := 1 - (cell13052 ⟨30,by decide⟩).lower)
        (by norm_num [cell13052]) (by norm_num [cell13052])
      exact ⟨E.1,E.2.trans (by norm_num [cell13052])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy31 (n := 13052) (by norm_num)
        (q := 1 - (cell13052 ⟨31,by decide⟩).lower)
        (by norm_num [cell13052]) (by norm_num [cell13052])
      exact ⟨E.1,E.2.trans (by norm_num [cell13052])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy32 (n := 13052) (by norm_num)
        (q := 1 - (cell13052 ⟨32,by decide⟩).lower)
        (by norm_num [cell13052]) (by norm_num [cell13052])
      exact ⟨E.1,E.2.trans (by norm_num [cell13052])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy33 (n := 13052) (by norm_num)
        (q := 1 - (cell13052 ⟨33,by decide⟩).lower)
        (by norm_num [cell13052]) (by norm_num [cell13052])
      exact ⟨E.1,E.2.trans (by norm_num [cell13052])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy34 (n := 13052) (by norm_num)
        (q := 1 - (cell13052 ⟨34,by decide⟩).lower)
        (by norm_num [cell13052]) (by norm_num [cell13052])
      exact ⟨E.1,E.2.trans (by norm_num [cell13052])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy35 (n := 13052) (by norm_num)
        (q := 1 - (cell13052 ⟨35,by decide⟩).lower)
        (by norm_num [cell13052]) (by norm_num [cell13052])
      exact ⟨E.1,E.2.trans (by norm_num [cell13052])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy36 (n := 13052) (by norm_num)
        (q := 1 - (cell13052 ⟨36,by decide⟩).lower)
        (by norm_num [cell13052]) (by norm_num [cell13052])
      exact ⟨E.1,E.2.trans (by norm_num [cell13052])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy37 (n := 13052) (by norm_num)
        (q := 1 - (cell13052 ⟨37,by decide⟩).lower)
        (by norm_num [cell13052]) (by norm_num [cell13052])
      exact ⟨E.1,E.2.trans (by norm_num [cell13052])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy38 (n := 13052) (by norm_num)
        (q := 1 - (cell13052 ⟨38,by decide⟩).lower)
        (by norm_num [cell13052]) (by norm_num [cell13052])
      exact ⟨E.1,E.2.trans (by norm_num [cell13052])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy39 (n := 13052) (by norm_num)
        (q := 1 - (cell13052 ⟨39,by decide⟩).lower)
        (by norm_num [cell13052]) (by norm_num [cell13052])
      exact ⟨E.1,E.2.trans (by norm_num [cell13052])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy40 (n := 13052) (by norm_num)
        (q := 1 - (cell13052 ⟨40,by decide⟩).lower)
        (by norm_num [cell13052]) (by norm_num [cell13052])
      exact ⟨E.1,E.2.trans (by norm_num [cell13052])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy41 (n := 13052) (by norm_num)
        (q := 1 - (cell13052 ⟨41,by decide⟩).lower)
        (by norm_num [cell13052]) (by norm_num [cell13052])
      exact ⟨E.1,E.2.trans (by norm_num [cell13052])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy42 (n := 13052) (by norm_num)
        (q := 1 - (cell13052 ⟨42,by decide⟩).lower)
        (by norm_num [cell13052]) (by norm_num [cell13052])
      exact ⟨E.1,E.2.trans (by norm_num [cell13052])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy43 (n := 13052) (by norm_num)
        (q := 1 - (cell13052 ⟨43,by decide⟩).lower)
        (by norm_num [cell13052]) (by norm_num [cell13052])
      exact ⟨E.1,E.2.trans (by norm_num [cell13052])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy44 (n := 13052) (by norm_num)
        (q := 1 - (cell13052 ⟨44,by decide⟩).lower)
        (by norm_num [cell13052]) (by norm_num [cell13052])
      exact ⟨E.1,E.2.trans (by norm_num [cell13052])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy45 (n := 13052) (by norm_num)
        (q := 1 - (cell13052 ⟨45,by decide⟩).lower)
        (by norm_num [cell13052]) (by norm_num [cell13052])
      exact ⟨E.1,E.2.trans (by norm_num [cell13052])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy46 (n := 13052) (by norm_num)
        (q := 1 - (cell13052 ⟨46,by decide⟩).lower)
        (by norm_num [cell13052]) (by norm_num [cell13052])
      exact ⟨E.1,E.2.trans (by norm_num [cell13052])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy47 (n := 13052) (by norm_num)
        (q := 1 - (cell13052 ⟨47,by decide⟩).lower)
        (by norm_num [cell13052]) (by norm_num [cell13052])
      exact ⟨E.1,E.2.trans (by norm_num [cell13052])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy48 (n := 13052) (by norm_num)
        (q := 1 - (cell13052 ⟨48,by decide⟩).lower)
        (by norm_num [cell13052]) (by norm_num [cell13052])
      exact ⟨E.1,E.2.trans (by norm_num [cell13052])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy49 (n := 13052) (by norm_num)
        (q := 1 - (cell13052 ⟨49,by decide⟩).lower)
        (by norm_num [cell13052]) (by norm_num [cell13052])
      exact ⟨E.1,E.2.trans (by norm_num [cell13052])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy50 (n := 13052) (by norm_num)
        (q := 1 - (cell13052 ⟨50,by decide⟩).lower)
        (by norm_num [cell13052]) (by norm_num [cell13052])
      exact ⟨E.1,E.2.trans (by norm_num [cell13052])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy51 (n := 13052) (by norm_num)
        (q := 1 - (cell13052 ⟨51,by decide⟩).lower)
        (by norm_num [cell13052]) (by norm_num [cell13052])
      exact ⟨E.1,E.2.trans (by norm_num [cell13052])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy52 (n := 13052) (by norm_num)
        (q := 1 - (cell13052 ⟨52,by decide⟩).lower)
        (by norm_num [cell13052]) (by norm_num [cell13052])
      exact ⟨E.1,E.2.trans (by norm_num [cell13052])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13052

/-! Source-cell containment and simple scalar guards at 13052. -/
namespace BstLean.Part269.N13052
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13052)
open BstLean.Part268 (cell13052)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13052 ⟨10,by decide⟩).lower ∧ (cell13052 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13052 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13052 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13052 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13052 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13052 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13052,cell13052,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13052 ⟨11,by decide⟩).lower ∧ (cell13052 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13052 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13052 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13052 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13052 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13052 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13052,cell13052,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13052 ⟨12,by decide⟩).lower ∧ (cell13052 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13052 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13052 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13052 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13052 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13052 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13052,cell13052,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13052 ⟨13,by decide⟩).lower ∧ (cell13052 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13052 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13052 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13052 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13052 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13052 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13052,cell13052,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13052 ⟨14,by decide⟩).lower ∧ (cell13052 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13052 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13052 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13052 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13052 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13052 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13052,cell13052,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13052 ⟨15,by decide⟩).lower ∧ (cell13052 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13052 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13052 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13052 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13052 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13052 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13052,cell13052,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13052 ⟨16,by decide⟩).lower ∧ (cell13052 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13052 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13052 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13052 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13052 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13052 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13052,cell13052,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13052 ⟨17,by decide⟩).lower ∧ (cell13052 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13052 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13052 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13052 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13052 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13052 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13052,cell13052,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13052 ⟨18,by decide⟩).lower ∧ (cell13052 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13052 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13052 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13052 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13052 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13052 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13052,cell13052,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13052 ⟨19,by decide⟩).lower ∧ (cell13052 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13052 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13052 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13052 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13052 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13052 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13052,cell13052,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13052 ⟨20,by decide⟩).lower ∧ (cell13052 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13052 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13052 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13052 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13052 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13052 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13052,cell13052,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13052 ⟨21,by decide⟩).lower ∧ (cell13052 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13052 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13052 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13052 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13052 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13052 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13052,cell13052,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13052 ⟨22,by decide⟩).lower ∧ (cell13052 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13052 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13052 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13052 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13052 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13052 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13052,cell13052,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13052 ⟨23,by decide⟩).lower ∧ (cell13052 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13052 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13052 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13052 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13052 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13052 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13052,cell13052,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13052 ⟨24,by decide⟩).lower ∧ (cell13052 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13052 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13052 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13052 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13052 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13052 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13052,cell13052,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13052 ⟨25,by decide⟩).lower ∧ (cell13052 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13052 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13052 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13052 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13052 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13052 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13052,cell13052,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13052 ⟨26,by decide⟩).lower ∧ (cell13052 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13052 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13052 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13052 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13052 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13052 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13052,cell13052,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13052 ⟨27,by decide⟩).lower ∧ (cell13052 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13052 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13052 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13052 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13052 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13052 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13052,cell13052,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13052 ⟨28,by decide⟩).lower ∧ (cell13052 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13052 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13052 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13052 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13052 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13052 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13052,cell13052,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13052 ⟨29,by decide⟩).lower ∧ (cell13052 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13052 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13052 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13052 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13052 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13052 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13052,cell13052,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13052 ⟨30,by decide⟩).lower ∧ (cell13052 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13052 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13052 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13052 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13052 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13052 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13052,cell13052,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13052 ⟨31,by decide⟩).lower ∧ (cell13052 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13052 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13052 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13052 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13052 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13052 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13052,cell13052,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13052 ⟨32,by decide⟩).lower ∧ (cell13052 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13052 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13052 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13052 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13052 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13052 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13052,cell13052,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13052 ⟨33,by decide⟩).lower ∧ (cell13052 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13052 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13052 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13052 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13052 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13052 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13052,cell13052,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13052 ⟨34,by decide⟩).lower ∧ (cell13052 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13052 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13052 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13052 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13052 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13052 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13052,cell13052,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13052 ⟨35,by decide⟩).lower ∧ (cell13052 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13052 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13052 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13052 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13052 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13052 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13052,cell13052,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13052 ⟨36,by decide⟩).lower ∧ (cell13052 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13052 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13052 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13052 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13052 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13052 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13052,cell13052,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13052 ⟨37,by decide⟩).lower ∧ (cell13052 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13052 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13052 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13052 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13052 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13052 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13052,cell13052,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13052 ⟨38,by decide⟩).lower ∧ (cell13052 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13052 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13052 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13052 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13052 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13052 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13052,cell13052,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13052 ⟨39,by decide⟩).lower ∧ (cell13052 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13052 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13052 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13052 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13052 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13052 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13052,cell13052,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13052 ⟨40,by decide⟩).lower ∧ (cell13052 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13052 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13052 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13052 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13052 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13052 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13052,cell13052,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13052 ⟨41,by decide⟩).lower ∧ (cell13052 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13052 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13052 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13052 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13052 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13052 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13052,cell13052,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13052 ⟨42,by decide⟩).lower ∧ (cell13052 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13052 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13052 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13052 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13052 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13052 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13052,cell13052,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13052 ⟨43,by decide⟩).lower ∧ (cell13052 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13052 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13052 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13052 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13052 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13052 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13052,cell13052,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13052 ⟨44,by decide⟩).lower ∧ (cell13052 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13052 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13052 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13052 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13052 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13052 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13052,cell13052,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13052 ⟨45,by decide⟩).lower ∧ (cell13052 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13052 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13052 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13052 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13052 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13052 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13052,cell13052,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13052 ⟨46,by decide⟩).lower ∧ (cell13052 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13052 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13052 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13052 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13052 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13052 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13052,cell13052,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13052 ⟨47,by decide⟩).lower ∧ (cell13052 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13052 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13052 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13052 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13052 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13052 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13052,cell13052,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13052 ⟨48,by decide⟩).lower ∧ (cell13052 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13052 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13052 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13052 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13052 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13052 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13052,cell13052,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13052 ⟨49,by decide⟩).lower ∧ (cell13052 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13052 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13052 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13052 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13052 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13052 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13052,cell13052,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13052 ⟨50,by decide⟩).lower ∧ (cell13052 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13052 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13052 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13052 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13052 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13052 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13052,cell13052,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13052 ⟨51,by decide⟩).lower ∧ (cell13052 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13052 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13052 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13052 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13052 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13052 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13052,cell13052,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13052 ⟨52,by decide⟩).lower ∧ (cell13052 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13052 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13052 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13052 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13052 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13052 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13052,cell13052,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13052 i).lower ∧
    (cell13052 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13052 i).upper ≤ (0.532 : ℝ) ∧
    (cell13052 i).centre ≤ (0.1 : ℝ) ∧ (cell13052 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13052 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13052 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13052

/-! The local source numeric instances at 13052 have no network premises. -/
namespace BstLean.Part269.N13052
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13052)
open BstLean.Part268 (cell13052)

noncomputable def sourceNumerics13052 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13052 (cell13052 i)
      scalarRow13052.M scalarRow13052.H scalarRow13052.xi := by
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
    energy_allowance := scalarRow13052.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13052]
    centre_nonneg := (scalarRow13052.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D28.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13052])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13052
/-! Actual 13053 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13053
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13053 ≤ (1.035317467702 : ℝ) := by
  have hr : (114.249726476696 : ℝ) ≤ √(13053 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.249726476696 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13053 13053 (11 / 1000) ≤
    (0.008366645236 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13053) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.249726476696 : ℝ) ≤ √(13053 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13053)
  have hdiv : K / √(13053 : ℝ) ≤ K / 114.249726476696 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.249726476696 ≤ (0.008366645236 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13053.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13053 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13053 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13053 := gPlus_lower 13053
end BstLean.Part269.N13053

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13053
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035317467701 : ℝ) ≤ wn 13053 := by
  have hn : √(13053 : ℝ) ≤ 114.249726476697 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13053 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.249726476697 ≤ 2 / √(13053 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000244952758 : ℝ) ≤ rhoBar 13053 BstLean.Part154.csC ∧
    rhoBar 13053 BstLean.Part154.csC ≤ 0.000244953138 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035317467701 : ℝ) / (1.295212 * 13053) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035317467702 : ℝ) / (1.29521 * 13053) := by gcongr
      _ ≤ (0.000244953138 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13053 BstLean.Part154.csC) ≤ 0.000979872555 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13053 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13053 BstLean.Part154.csC) (piBar (rhoBar 13053 BstLean.Part154.csC)) ≤ 0.000187096620 ∧
    cc1 (rhoBar 13053 BstLean.Part154.csC) (piBar (rhoBar 13053 BstLean.Part154.csC)) ≤ 0.000119050871 ∧
    cc2 (rhoBar 13053 BstLean.Part154.csC) ≤ 0.000069110002 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13053 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13053 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13053 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13053 BstLean.Part154.csC * nuR (rhoBar 13053 BstLean.Part154.csC)) ≤ 0.000489921277 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000244953138 : ℝ) * 0.000979872555 := by gcongr
      _ ≤ (0.000489921277 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13053 BstLean.Part154.csC) * nuR (rhoBar 13053 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000979872555 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13053 BstLean.Part154.csC) * rhoBar 13053 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000244953138 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000244953138 / 2 + 0.399 * 0.000979872555 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000187096620 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000489921277 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119050871 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000244953138 / 1.414213562 := by gcongr
      _ ≤ (0.000069110002 : ℝ) := by norm_num

end BstLean.Part269.N13053

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13053
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13053 BstLean.Part154.csC) (piBar (rhoBar 13053 BstLean.Part154.csC)) ≤ 1.51171E-7 := by
  have hr0 : 0 ≤ rhoBar 13053 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13053 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13053 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13053 BstLean.Part154.csC) (piBar (rhoBar 13053 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13053 BstLean.Part154.csC) (piBar (rhoBar 13053 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13053 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000187096620 : ℝ) ^ 2 + 0.000119050871 ^ 2 + 3 * 0.000069110002 ^ 2 +
        2 * 0.797885 * 0.000187096620 * 0.000119050871 + 2 * 0.000187096620 * 0.000069110002 +
        4 * 0.797885 * 0.000119050871 * 0.000069110002 := by gcongr
    _ ≤ (1.51171E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13053 BstLean.Part154.csC Θ ≤ 0.002555757742 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13053 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13053 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13053 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13053 BstLean.Part154.csC) (piBar (rhoBar 13053 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13053 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035317467702 * 1.51171E-7 / (0.000244952758 : ℝ) := by gcongr
    _ ≤ 0.002555757742 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13053 BstLean.Part154.csC Θ ≤ 0.002834397058 + 0.000645798086 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13053 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13053 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13053 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035317467702 : ℝ) * ((2 * Θ * 0.000244953138 +
        (6863 / 10000) * 0.000244953138 * 13053 * 0.000979872555) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002834397058 + 0.000645798086 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13053 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13053 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13053 0.011 Θ ∧ gammaRatio 13053 0.011 Θ ≤ 0.000084208555 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13053 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035317467702 : ℝ) * 0.525 / ((1 - 0.011) * 13053) := by gcongr
      _ ≤ (0.000084208555 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13053 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13053 0.011 Θ) :=
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
    badAllowance 13053 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000383749387 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13053 BstLean.Part154.csC) 1.22 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 2 (rhoBar 13053 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13053 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13053 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13053 0.011 Θ) 1.12 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 1 (gammaRatio 13053 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13053 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13053 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13053 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13053 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035317467702 : ℝ) * 13053 *
        (1.3781E-8 / 1.1045361 + 1.6832E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000383749387 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13053 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003218146445 + 0.003201555828 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13053

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13053
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13053 BstLean.Part154.csC) (piBar (rhoBar 13053 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13053 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13053 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13053 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13053 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13053 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13053 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13053 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13053 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13053 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13053 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13053 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13053 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13053 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13053 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051762123884 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13053) ≤ 0.010452870374 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13053 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035317467702)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010452870374 + 2 * 0.737676 / 13053) := by gcongr
    _ ≤ (0.051762123884 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13053 12 ≤ 0.0015 := by
  exact BstLean.Part269.S28.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13053

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13053
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560519100283 : ℝ) ≤ plow 13053 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13053) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052405563255)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001341772815) : eMP 13053 0.011 xi bn ≤ 0.001155608253 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13053 : ℝ) * (1 - 0.011))) ≤ 0.000571427504 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001341772815 / (13053 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000571427504 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000571427504 : ℝ) + 3.141593 * 0.052405563255 / (13053 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001155608253 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052405563255)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001341772815) : PiBarMP 13053 12 0.011 xi bn ≤ 0.159034117444 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13053 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036630217240 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.619615383964 : ℝ) ≤ √((13053 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.249726476696 : ℝ) ≤ √(13053 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13053) ≤ 0.121946972588 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036630217240 + 0.052405563255 * 1.772454 / (2 * (113.619615383964 : ℝ))) * (1 + 0.001155608253) +
        8 / (13053 * 114.249726476696) + 0.121946972588 := by gcongr
    _ ≤ (0.159034117444 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052405563255)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001341772815) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280684738003) :
    parallelOracle 13053 0.011 xi bn cd ≤ 0.159997765184 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13053 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13053 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560519100283 : ℝ) ≤ plow 13053 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.249726476696 : ℝ) ≤ √(13053 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280684738003 : ℝ) / (2 * 0.560519100283 * 114.249726476696)) * 0.159034117444 +
        0.280684738003 ^ 2 / (2 * 0.560519100283 * 114.249726476696) := by gcongr
    _ ≤ (0.159997765184 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052405563255) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001341772815)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280684738003) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13053 13053 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560519100283 : ℝ) ≤ plow 13053 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.249726476696 : ℝ) ≤ √(13053 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13053 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13053 Θ 1.22 ≤ 0.011607034353 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.249726476696 := by gcongr <;> linarith
      _ ≤ (0.011607034353 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13053 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13053 13053 0.011 ≤ 0.008366645236 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13053 13053 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13053 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13053 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13053 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13053 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159997765184 + 0.011607034353 + (0.008366645236 : ℝ) *
        (1 + 2 * (0.280684738003 + 0.011607034353) / (0.560519100283 * 114.249726476696))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13053]

end BstLean.Part269.N13053

/-! The original eight local profiles supply actual 13053 moment certificates. -/
namespace BstLean.Part269.N13053
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13053 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13053 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13053 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052405563255 ∧
    0 ≤ bN 13053 BstLean.Part154.csC (groupTheta g) ∧ bN 13053 BstLean.Part154.csC (groupTheta g) ≤ 0.001341772815 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13053 13053 0.011
      (momentAllowance 13053 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13053 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13053 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13053 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13053 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13053 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228922614119 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13053 0.011
      (momentAllowance 13053 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13053 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13053
/-! The actual computed-centre upper energy formula at 13053. -/
namespace BstLean.Part269.N13053
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13053

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13053
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13053)
open BstLean.Part268 (cell13053)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084522444277
  | 2 => 0.085449325007
  | 3 => 0.086372145447
  | 4 => 0.087291806654
  | 5 => 0.088209413522
  | 6 => 0.089126306905
  | 7 => 0.090044099123
  | 8 => 0.090964712940
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13053 13053 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13053 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003218831707 + 0.003202305177 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S28.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13053

/-! Actual upper energy certificates on all 43 source endpoints at 13053. -/
namespace BstLean.Part269.N13053
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13053)
open BstLean.Part268 (cell13053)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13053 (gMinus 13053) (1 - (cell13053 i).lower) ≤ 1 ∧
    energyUpper 13053 (gMinus 13053) (BstLean.Part211.gPlus 13053)
      (finiteEnergy 13053 13053 0.011) (1 - (cell13053 i).lower) ≤
      (cell13053 i).energy := by
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
      have E := BstLean.Part269.S28.uniformEnergy10 (n := 13053) (by norm_num)
        (q := 1 - (cell13053 ⟨10,by decide⟩).lower)
        (by norm_num [cell13053]) (by norm_num [cell13053])
      exact ⟨E.1,E.2.trans (by norm_num [cell13053])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy11 (n := 13053) (by norm_num)
        (q := 1 - (cell13053 ⟨11,by decide⟩).lower)
        (by norm_num [cell13053]) (by norm_num [cell13053])
      exact ⟨E.1,E.2.trans (by norm_num [cell13053])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy12 (n := 13053) (by norm_num)
        (q := 1 - (cell13053 ⟨12,by decide⟩).lower)
        (by norm_num [cell13053]) (by norm_num [cell13053])
      exact ⟨E.1,E.2.trans (by norm_num [cell13053])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy13 (n := 13053) (by norm_num)
        (q := 1 - (cell13053 ⟨13,by decide⟩).lower)
        (by norm_num [cell13053]) (by norm_num [cell13053])
      exact ⟨E.1,E.2.trans (by norm_num [cell13053])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy14 (n := 13053) (by norm_num)
        (q := 1 - (cell13053 ⟨14,by decide⟩).lower)
        (by norm_num [cell13053]) (by norm_num [cell13053])
      exact ⟨E.1,E.2.trans (by norm_num [cell13053])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy15 (n := 13053) (by norm_num)
        (q := 1 - (cell13053 ⟨15,by decide⟩).lower)
        (by norm_num [cell13053]) (by norm_num [cell13053])
      exact ⟨E.1,E.2.trans (by norm_num [cell13053])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy16 (n := 13053) (by norm_num)
        (q := 1 - (cell13053 ⟨16,by decide⟩).lower)
        (by norm_num [cell13053]) (by norm_num [cell13053])
      exact ⟨E.1,E.2.trans (by norm_num [cell13053])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy17 (n := 13053) (by norm_num)
        (q := 1 - (cell13053 ⟨17,by decide⟩).lower)
        (by norm_num [cell13053]) (by norm_num [cell13053])
      exact ⟨E.1,E.2.trans (by norm_num [cell13053])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy18 (n := 13053) (by norm_num)
        (q := 1 - (cell13053 ⟨18,by decide⟩).lower)
        (by norm_num [cell13053]) (by norm_num [cell13053])
      exact ⟨E.1,E.2.trans (by norm_num [cell13053])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy19 (n := 13053) (by norm_num)
        (q := 1 - (cell13053 ⟨19,by decide⟩).lower)
        (by norm_num [cell13053]) (by norm_num [cell13053])
      exact ⟨E.1,E.2.trans (by norm_num [cell13053])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy20 (n := 13053) (by norm_num)
        (q := 1 - (cell13053 ⟨20,by decide⟩).lower)
        (by norm_num [cell13053]) (by norm_num [cell13053])
      exact ⟨E.1,E.2.trans (by norm_num [cell13053])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy21 (n := 13053) (by norm_num)
        (q := 1 - (cell13053 ⟨21,by decide⟩).lower)
        (by norm_num [cell13053]) (by norm_num [cell13053])
      exact ⟨E.1,E.2.trans (by norm_num [cell13053])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy22 (n := 13053) (by norm_num)
        (q := 1 - (cell13053 ⟨22,by decide⟩).lower)
        (by norm_num [cell13053]) (by norm_num [cell13053])
      exact ⟨E.1,E.2.trans (by norm_num [cell13053])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy23 (n := 13053) (by norm_num)
        (q := 1 - (cell13053 ⟨23,by decide⟩).lower)
        (by norm_num [cell13053]) (by norm_num [cell13053])
      exact ⟨E.1,E.2.trans (by norm_num [cell13053])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy24 (n := 13053) (by norm_num)
        (q := 1 - (cell13053 ⟨24,by decide⟩).lower)
        (by norm_num [cell13053]) (by norm_num [cell13053])
      exact ⟨E.1,E.2.trans (by norm_num [cell13053])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy25 (n := 13053) (by norm_num)
        (q := 1 - (cell13053 ⟨25,by decide⟩).lower)
        (by norm_num [cell13053]) (by norm_num [cell13053])
      exact ⟨E.1,E.2.trans (by norm_num [cell13053])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy26 (n := 13053) (by norm_num)
        (q := 1 - (cell13053 ⟨26,by decide⟩).lower)
        (by norm_num [cell13053]) (by norm_num [cell13053])
      exact ⟨E.1,E.2.trans (by norm_num [cell13053])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy27 (n := 13053) (by norm_num)
        (q := 1 - (cell13053 ⟨27,by decide⟩).lower)
        (by norm_num [cell13053]) (by norm_num [cell13053])
      exact ⟨E.1,E.2.trans (by norm_num [cell13053])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy28 (n := 13053) (by norm_num)
        (q := 1 - (cell13053 ⟨28,by decide⟩).lower)
        (by norm_num [cell13053]) (by norm_num [cell13053])
      exact ⟨E.1,E.2.trans (by norm_num [cell13053])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy29 (n := 13053) (by norm_num)
        (q := 1 - (cell13053 ⟨29,by decide⟩).lower)
        (by norm_num [cell13053]) (by norm_num [cell13053])
      exact ⟨E.1,E.2.trans (by norm_num [cell13053])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy30 (n := 13053) (by norm_num)
        (q := 1 - (cell13053 ⟨30,by decide⟩).lower)
        (by norm_num [cell13053]) (by norm_num [cell13053])
      exact ⟨E.1,E.2.trans (by norm_num [cell13053])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy31 (n := 13053) (by norm_num)
        (q := 1 - (cell13053 ⟨31,by decide⟩).lower)
        (by norm_num [cell13053]) (by norm_num [cell13053])
      exact ⟨E.1,E.2.trans (by norm_num [cell13053])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy32 (n := 13053) (by norm_num)
        (q := 1 - (cell13053 ⟨32,by decide⟩).lower)
        (by norm_num [cell13053]) (by norm_num [cell13053])
      exact ⟨E.1,E.2.trans (by norm_num [cell13053])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy33 (n := 13053) (by norm_num)
        (q := 1 - (cell13053 ⟨33,by decide⟩).lower)
        (by norm_num [cell13053]) (by norm_num [cell13053])
      exact ⟨E.1,E.2.trans (by norm_num [cell13053])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy34 (n := 13053) (by norm_num)
        (q := 1 - (cell13053 ⟨34,by decide⟩).lower)
        (by norm_num [cell13053]) (by norm_num [cell13053])
      exact ⟨E.1,E.2.trans (by norm_num [cell13053])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy35 (n := 13053) (by norm_num)
        (q := 1 - (cell13053 ⟨35,by decide⟩).lower)
        (by norm_num [cell13053]) (by norm_num [cell13053])
      exact ⟨E.1,E.2.trans (by norm_num [cell13053])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy36 (n := 13053) (by norm_num)
        (q := 1 - (cell13053 ⟨36,by decide⟩).lower)
        (by norm_num [cell13053]) (by norm_num [cell13053])
      exact ⟨E.1,E.2.trans (by norm_num [cell13053])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy37 (n := 13053) (by norm_num)
        (q := 1 - (cell13053 ⟨37,by decide⟩).lower)
        (by norm_num [cell13053]) (by norm_num [cell13053])
      exact ⟨E.1,E.2.trans (by norm_num [cell13053])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy38 (n := 13053) (by norm_num)
        (q := 1 - (cell13053 ⟨38,by decide⟩).lower)
        (by norm_num [cell13053]) (by norm_num [cell13053])
      exact ⟨E.1,E.2.trans (by norm_num [cell13053])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy39 (n := 13053) (by norm_num)
        (q := 1 - (cell13053 ⟨39,by decide⟩).lower)
        (by norm_num [cell13053]) (by norm_num [cell13053])
      exact ⟨E.1,E.2.trans (by norm_num [cell13053])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy40 (n := 13053) (by norm_num)
        (q := 1 - (cell13053 ⟨40,by decide⟩).lower)
        (by norm_num [cell13053]) (by norm_num [cell13053])
      exact ⟨E.1,E.2.trans (by norm_num [cell13053])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy41 (n := 13053) (by norm_num)
        (q := 1 - (cell13053 ⟨41,by decide⟩).lower)
        (by norm_num [cell13053]) (by norm_num [cell13053])
      exact ⟨E.1,E.2.trans (by norm_num [cell13053])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy42 (n := 13053) (by norm_num)
        (q := 1 - (cell13053 ⟨42,by decide⟩).lower)
        (by norm_num [cell13053]) (by norm_num [cell13053])
      exact ⟨E.1,E.2.trans (by norm_num [cell13053])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy43 (n := 13053) (by norm_num)
        (q := 1 - (cell13053 ⟨43,by decide⟩).lower)
        (by norm_num [cell13053]) (by norm_num [cell13053])
      exact ⟨E.1,E.2.trans (by norm_num [cell13053])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy44 (n := 13053) (by norm_num)
        (q := 1 - (cell13053 ⟨44,by decide⟩).lower)
        (by norm_num [cell13053]) (by norm_num [cell13053])
      exact ⟨E.1,E.2.trans (by norm_num [cell13053])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy45 (n := 13053) (by norm_num)
        (q := 1 - (cell13053 ⟨45,by decide⟩).lower)
        (by norm_num [cell13053]) (by norm_num [cell13053])
      exact ⟨E.1,E.2.trans (by norm_num [cell13053])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy46 (n := 13053) (by norm_num)
        (q := 1 - (cell13053 ⟨46,by decide⟩).lower)
        (by norm_num [cell13053]) (by norm_num [cell13053])
      exact ⟨E.1,E.2.trans (by norm_num [cell13053])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy47 (n := 13053) (by norm_num)
        (q := 1 - (cell13053 ⟨47,by decide⟩).lower)
        (by norm_num [cell13053]) (by norm_num [cell13053])
      exact ⟨E.1,E.2.trans (by norm_num [cell13053])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy48 (n := 13053) (by norm_num)
        (q := 1 - (cell13053 ⟨48,by decide⟩).lower)
        (by norm_num [cell13053]) (by norm_num [cell13053])
      exact ⟨E.1,E.2.trans (by norm_num [cell13053])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy49 (n := 13053) (by norm_num)
        (q := 1 - (cell13053 ⟨49,by decide⟩).lower)
        (by norm_num [cell13053]) (by norm_num [cell13053])
      exact ⟨E.1,E.2.trans (by norm_num [cell13053])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy50 (n := 13053) (by norm_num)
        (q := 1 - (cell13053 ⟨50,by decide⟩).lower)
        (by norm_num [cell13053]) (by norm_num [cell13053])
      exact ⟨E.1,E.2.trans (by norm_num [cell13053])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy51 (n := 13053) (by norm_num)
        (q := 1 - (cell13053 ⟨51,by decide⟩).lower)
        (by norm_num [cell13053]) (by norm_num [cell13053])
      exact ⟨E.1,E.2.trans (by norm_num [cell13053])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy52 (n := 13053) (by norm_num)
        (q := 1 - (cell13053 ⟨52,by decide⟩).lower)
        (by norm_num [cell13053]) (by norm_num [cell13053])
      exact ⟨E.1,E.2.trans (by norm_num [cell13053])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13053

/-! Source-cell containment and simple scalar guards at 13053. -/
namespace BstLean.Part269.N13053
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13053)
open BstLean.Part268 (cell13053)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13053 ⟨10,by decide⟩).lower ∧ (cell13053 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13053 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13053 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13053 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13053 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13053 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13053,cell13053,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13053 ⟨11,by decide⟩).lower ∧ (cell13053 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13053 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13053 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13053 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13053 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13053 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13053,cell13053,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13053 ⟨12,by decide⟩).lower ∧ (cell13053 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13053 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13053 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13053 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13053 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13053 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13053,cell13053,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13053 ⟨13,by decide⟩).lower ∧ (cell13053 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13053 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13053 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13053 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13053 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13053 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13053,cell13053,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13053 ⟨14,by decide⟩).lower ∧ (cell13053 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13053 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13053 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13053 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13053 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13053 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13053,cell13053,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13053 ⟨15,by decide⟩).lower ∧ (cell13053 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13053 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13053 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13053 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13053 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13053 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13053,cell13053,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13053 ⟨16,by decide⟩).lower ∧ (cell13053 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13053 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13053 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13053 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13053 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13053 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13053,cell13053,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13053 ⟨17,by decide⟩).lower ∧ (cell13053 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13053 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13053 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13053 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13053 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13053 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13053,cell13053,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13053 ⟨18,by decide⟩).lower ∧ (cell13053 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13053 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13053 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13053 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13053 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13053 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13053,cell13053,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13053 ⟨19,by decide⟩).lower ∧ (cell13053 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13053 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13053 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13053 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13053 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13053 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13053,cell13053,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13053 ⟨20,by decide⟩).lower ∧ (cell13053 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13053 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13053 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13053 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13053 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13053 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13053,cell13053,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13053 ⟨21,by decide⟩).lower ∧ (cell13053 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13053 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13053 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13053 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13053 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13053 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13053,cell13053,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13053 ⟨22,by decide⟩).lower ∧ (cell13053 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13053 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13053 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13053 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13053 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13053 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13053,cell13053,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13053 ⟨23,by decide⟩).lower ∧ (cell13053 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13053 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13053 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13053 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13053 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13053 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13053,cell13053,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13053 ⟨24,by decide⟩).lower ∧ (cell13053 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13053 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13053 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13053 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13053 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13053 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13053,cell13053,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13053 ⟨25,by decide⟩).lower ∧ (cell13053 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13053 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13053 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13053 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13053 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13053 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13053,cell13053,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13053 ⟨26,by decide⟩).lower ∧ (cell13053 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13053 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13053 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13053 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13053 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13053 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13053,cell13053,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13053 ⟨27,by decide⟩).lower ∧ (cell13053 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13053 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13053 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13053 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13053 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13053 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13053,cell13053,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13053 ⟨28,by decide⟩).lower ∧ (cell13053 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13053 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13053 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13053 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13053 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13053 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13053,cell13053,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13053 ⟨29,by decide⟩).lower ∧ (cell13053 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13053 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13053 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13053 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13053 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13053 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13053,cell13053,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13053 ⟨30,by decide⟩).lower ∧ (cell13053 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13053 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13053 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13053 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13053 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13053 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13053,cell13053,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13053 ⟨31,by decide⟩).lower ∧ (cell13053 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13053 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13053 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13053 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13053 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13053 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13053,cell13053,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13053 ⟨32,by decide⟩).lower ∧ (cell13053 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13053 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13053 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13053 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13053 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13053 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13053,cell13053,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13053 ⟨33,by decide⟩).lower ∧ (cell13053 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13053 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13053 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13053 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13053 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13053 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13053,cell13053,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13053 ⟨34,by decide⟩).lower ∧ (cell13053 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13053 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13053 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13053 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13053 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13053 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13053,cell13053,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13053 ⟨35,by decide⟩).lower ∧ (cell13053 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13053 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13053 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13053 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13053 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13053 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13053,cell13053,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13053 ⟨36,by decide⟩).lower ∧ (cell13053 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13053 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13053 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13053 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13053 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13053 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13053,cell13053,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13053 ⟨37,by decide⟩).lower ∧ (cell13053 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13053 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13053 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13053 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13053 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13053 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13053,cell13053,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13053 ⟨38,by decide⟩).lower ∧ (cell13053 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13053 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13053 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13053 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13053 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13053 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13053,cell13053,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13053 ⟨39,by decide⟩).lower ∧ (cell13053 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13053 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13053 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13053 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13053 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13053 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13053,cell13053,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13053 ⟨40,by decide⟩).lower ∧ (cell13053 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13053 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13053 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13053 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13053 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13053 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13053,cell13053,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13053 ⟨41,by decide⟩).lower ∧ (cell13053 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13053 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13053 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13053 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13053 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13053 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13053,cell13053,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13053 ⟨42,by decide⟩).lower ∧ (cell13053 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13053 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13053 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13053 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13053 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13053 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13053,cell13053,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13053 ⟨43,by decide⟩).lower ∧ (cell13053 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13053 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13053 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13053 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13053 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13053 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13053,cell13053,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13053 ⟨44,by decide⟩).lower ∧ (cell13053 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13053 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13053 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13053 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13053 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13053 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13053,cell13053,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13053 ⟨45,by decide⟩).lower ∧ (cell13053 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13053 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13053 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13053 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13053 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13053 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13053,cell13053,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13053 ⟨46,by decide⟩).lower ∧ (cell13053 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13053 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13053 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13053 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13053 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13053 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13053,cell13053,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13053 ⟨47,by decide⟩).lower ∧ (cell13053 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13053 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13053 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13053 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13053 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13053 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13053,cell13053,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13053 ⟨48,by decide⟩).lower ∧ (cell13053 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13053 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13053 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13053 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13053 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13053 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13053,cell13053,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13053 ⟨49,by decide⟩).lower ∧ (cell13053 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13053 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13053 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13053 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13053 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13053 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13053,cell13053,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13053 ⟨50,by decide⟩).lower ∧ (cell13053 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13053 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13053 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13053 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13053 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13053 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13053,cell13053,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13053 ⟨51,by decide⟩).lower ∧ (cell13053 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13053 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13053 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13053 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13053 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13053 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13053,cell13053,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13053 ⟨52,by decide⟩).lower ∧ (cell13053 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13053 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13053 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13053 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13053 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13053 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13053,cell13053,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13053 i).lower ∧
    (cell13053 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13053 i).upper ≤ (0.532 : ℝ) ∧
    (cell13053 i).centre ≤ (0.1 : ℝ) ∧ (cell13053 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13053 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13053 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13053

/-! The local source numeric instances at 13053 have no network premises. -/
namespace BstLean.Part269.N13053
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13053)
open BstLean.Part268 (cell13053)

noncomputable def sourceNumerics13053 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13053 (cell13053 i)
      scalarRow13053.M scalarRow13053.H scalarRow13053.xi := by
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
    energy_allowance := scalarRow13053.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13053]
    centre_nonneg := (scalarRow13053.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D28.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13053])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13053
/-! Actual 13054 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13054
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13054 ≤ (1.035316103194 : ℝ) := by
  have hr : (114.254102770972 : ℝ) ≤ √(13054 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.254102770972 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13054 13054 (11 / 1000) ≤
    (0.008366324765 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13054) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.254102770972 : ℝ) ≤ √(13054 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13054)
  have hdiv : K / √(13054 : ℝ) ≤ K / 114.254102770972 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.254102770972 ≤ (0.008366324765 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13054.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13054 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13054 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13054 := gPlus_lower 13054
end BstLean.Part269.N13054

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13054
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035316103193 : ℝ) ≤ wn 13054 := by
  have hn : √(13054 : ℝ) ≤ 114.254102770973 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13054 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.254102770973 ≤ 2 / √(13054 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000244933671 : ℝ) ≤ rhoBar 13054 BstLean.Part154.csC ∧
    rhoBar 13054 BstLean.Part154.csC ≤ 0.000244934050 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035316103193 : ℝ) / (1.295212 * 13054) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035316103194 : ℝ) / (1.29521 * 13054) := by gcongr
      _ ≤ (0.000244934050 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13054 BstLean.Part154.csC) ≤ 0.000979796193 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13054 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13054 BstLean.Part154.csC) (piBar (rhoBar 13054 BstLean.Part154.csC)) ≤ 0.000187082040 ∧
    cc1 (rhoBar 13054 BstLean.Part154.csC) (piBar (rhoBar 13054 BstLean.Part154.csC)) ≤ 0.000119041594 ∧
    cc2 (rhoBar 13054 BstLean.Part154.csC) ≤ 0.000069104617 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13054 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13054 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13054 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13054 BstLean.Part154.csC * nuR (rhoBar 13054 BstLean.Part154.csC)) ≤ 0.000489883099 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000244934050 : ℝ) * 0.000979796193 := by gcongr
      _ ≤ (0.000489883099 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13054 BstLean.Part154.csC) * nuR (rhoBar 13054 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000979796193 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13054 BstLean.Part154.csC) * rhoBar 13054 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000244934050 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000244934050 / 2 + 0.399 * 0.000979796193 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000187082040 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000489883099 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119041594 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000244934050 / 1.414213562 := by gcongr
      _ ≤ (0.000069104617 : ℝ) := by norm_num

end BstLean.Part269.N13054

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13054
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13054 BstLean.Part154.csC) (piBar (rhoBar 13054 BstLean.Part154.csC)) ≤ 1.51147E-7 := by
  have hr0 : 0 ≤ rhoBar 13054 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13054 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13054 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13054 BstLean.Part154.csC) (piBar (rhoBar 13054 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13054 BstLean.Part154.csC) (piBar (rhoBar 13054 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13054 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000187082040 : ℝ) ^ 2 + 0.000119041594 ^ 2 + 3 * 0.000069104617 ^ 2 +
        2 * 0.797885 * 0.000187082040 * 0.000119041594 + 2 * 0.000187082040 * 0.000069104617 +
        4 * 0.797885 * 0.000119041594 * 0.000069104617 := by gcongr
    _ ≤ (1.51147E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13054 BstLean.Part154.csC Θ ≤ 0.002555547752 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13054 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13054 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13054 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13054 BstLean.Part154.csC) (piBar (rhoBar 13054 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13054 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035316103194 * 1.51147E-7 / (0.000244933671 : ℝ) := by gcongr
    _ ≤ 0.002555547752 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13054 BstLean.Part154.csC Θ ≤ 0.002834168695 + 0.000645746911 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13054 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13054 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13054 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035316103194 : ℝ) * ((2 * Θ * 0.000244934050 +
        (6863 / 10000) * 0.000244934050 * 13054 * 0.000979796193) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002834168695 + 0.000645746911 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13054 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13054 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13054 0.011 Θ ∧ gammaRatio 13054 0.011 Θ ≤ 0.000084201993 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13054 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035316103194 : ℝ) * 0.525 / ((1 - 0.011) * 13054) := by gcongr
      _ ≤ (0.000084201993 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13054 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13054 0.011 Θ) :=
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
    badAllowance 13054 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000383749387 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13054 BstLean.Part154.csC) 1.22 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 2 (rhoBar 13054 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13054 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13054 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13054 0.011 Θ) 1.12 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 1 (gammaRatio 13054 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13054 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13054 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13054 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13054 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035316103194 : ℝ) * 13054 *
        (1.3781E-8 / 1.1045361 + 1.6832E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000383749387 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13054 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003217918082 + 0.003201294663 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13054

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13054
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13054 BstLean.Part154.csC) (piBar (rhoBar 13054 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13054 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13054 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13054 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13054 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13054 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13054 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13054 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13054 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13054 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13054 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13054 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13054 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13054 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13054 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051760120023 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13054) ≤ 0.010452469996 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13054 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035316103194)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010452469996 + 2 * 0.737676 / 13054) := by gcongr
    _ ≤ (0.051760120023 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13054 12 ≤ 0.0015 := by
  exact BstLean.Part269.S28.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13054

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13054
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560519143090 : ℝ) ≤ plow 13054 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13054) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052405197781)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001341662570) : eMP 13054 0.011 xi bn ≤ 0.001155516463 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13054 : ℝ) * (1 - 0.011))) ≤ 0.000571382142 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001341662570 / (13054 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000571382142 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000571382142 : ℝ) + 3.141593 * 0.052405197781 / (13054 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001155516463 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052405197781)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001341662570) : PiBarMP 13054 12 0.011 xi bn ≤ 0.159027917336 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13054 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036628712372 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.623967542063 : ℝ) ≤ √((13054 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.254102770972 : ℝ) ≤ √(13054 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13054) ≤ 0.121942301632 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036628712372 + 0.052405197781 * 1.772454 / (2 * (113.623967542063 : ℝ))) * (1 + 0.001155516463) +
        8 / (13054 * 114.254102770972) + 0.121942301632 := by gcongr
    _ ≤ (0.159027917336 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052405197781)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001341662570) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280681935893) :
    parallelOracle 13054 0.011 xi bn cd ≤ 0.159991498744 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13054 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13054 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560519143090 : ℝ) ≤ plow 13054 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.254102770972 : ℝ) ≤ √(13054 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280681935893 : ℝ) / (2 * 0.560519143090 * 114.254102770972)) * 0.159027917336 +
        0.280681935893 ^ 2 / (2 * 0.560519143090 * 114.254102770972) := by gcongr
    _ ≤ (0.159991498744 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052405197781) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001341662570)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280681935893) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13054 13054 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560519143090 : ℝ) ≤ plow 13054 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.254102770972 : ℝ) ≤ √(13054 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13054 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13054 Θ 1.22 ≤ 0.011606589767 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.254102770972 := by gcongr <;> linarith
      _ ≤ (0.011606589767 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13054 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13054 13054 0.011 ≤ 0.008366324765 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13054 13054 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13054 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13054 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13054 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13054 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159991498744 + 0.011606589767 + (0.008366324765 : ℝ) *
        (1 + 2 * (0.280681935893 + 0.011606589767) / (0.560519143090 * 114.254102770972))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13054]

end BstLean.Part269.N13054

/-! The original eight local profiles supply actual 13054 moment certificates. -/
namespace BstLean.Part269.N13054
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13054 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13054 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13054 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052405197781 ∧
    0 ≤ bN 13054 BstLean.Part154.csC (groupTheta g) ∧ bN 13054 BstLean.Part154.csC (groupTheta g) ≤ 0.001341662570 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13054 13054 0.011
      (momentAllowance 13054 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13054 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13054 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13054 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13054 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13054 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228921815870 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13054 0.011
      (momentAllowance 13054 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13054 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13054
/-! The actual computed-centre upper energy formula at 13054. -/
namespace BstLean.Part269.N13054
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13054

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13054
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13054)
open BstLean.Part268 (cell13054)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084519867823
  | 2 => 0.085446715466
  | 3 => 0.086369497915
  | 4 => 0.087289115071
  | 5 => 0.088206670455
  | 6 => 0.089123503313
  | 7 => 0.090041224081
  | 8 => 0.090961753339
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13054 13054 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13054 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003218831707 + 0.003202305177 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S28.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13054

/-! Actual upper energy certificates on all 43 source endpoints at 13054. -/
namespace BstLean.Part269.N13054
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13054)
open BstLean.Part268 (cell13054)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13054 (gMinus 13054) (1 - (cell13054 i).lower) ≤ 1 ∧
    energyUpper 13054 (gMinus 13054) (BstLean.Part211.gPlus 13054)
      (finiteEnergy 13054 13054 0.011) (1 - (cell13054 i).lower) ≤
      (cell13054 i).energy := by
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
      have E := BstLean.Part269.S28.uniformEnergy10 (n := 13054) (by norm_num)
        (q := 1 - (cell13054 ⟨10,by decide⟩).lower)
        (by norm_num [cell13054]) (by norm_num [cell13054])
      exact ⟨E.1,E.2.trans (by norm_num [cell13054])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy11 (n := 13054) (by norm_num)
        (q := 1 - (cell13054 ⟨11,by decide⟩).lower)
        (by norm_num [cell13054]) (by norm_num [cell13054])
      exact ⟨E.1,E.2.trans (by norm_num [cell13054])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy12 (n := 13054) (by norm_num)
        (q := 1 - (cell13054 ⟨12,by decide⟩).lower)
        (by norm_num [cell13054]) (by norm_num [cell13054])
      exact ⟨E.1,E.2.trans (by norm_num [cell13054])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy13 (n := 13054) (by norm_num)
        (q := 1 - (cell13054 ⟨13,by decide⟩).lower)
        (by norm_num [cell13054]) (by norm_num [cell13054])
      exact ⟨E.1,E.2.trans (by norm_num [cell13054])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy14 (n := 13054) (by norm_num)
        (q := 1 - (cell13054 ⟨14,by decide⟩).lower)
        (by norm_num [cell13054]) (by norm_num [cell13054])
      exact ⟨E.1,E.2.trans (by norm_num [cell13054])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy15 (n := 13054) (by norm_num)
        (q := 1 - (cell13054 ⟨15,by decide⟩).lower)
        (by norm_num [cell13054]) (by norm_num [cell13054])
      exact ⟨E.1,E.2.trans (by norm_num [cell13054])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy16 (n := 13054) (by norm_num)
        (q := 1 - (cell13054 ⟨16,by decide⟩).lower)
        (by norm_num [cell13054]) (by norm_num [cell13054])
      exact ⟨E.1,E.2.trans (by norm_num [cell13054])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy17 (n := 13054) (by norm_num)
        (q := 1 - (cell13054 ⟨17,by decide⟩).lower)
        (by norm_num [cell13054]) (by norm_num [cell13054])
      exact ⟨E.1,E.2.trans (by norm_num [cell13054])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy18 (n := 13054) (by norm_num)
        (q := 1 - (cell13054 ⟨18,by decide⟩).lower)
        (by norm_num [cell13054]) (by norm_num [cell13054])
      exact ⟨E.1,E.2.trans (by norm_num [cell13054])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy19 (n := 13054) (by norm_num)
        (q := 1 - (cell13054 ⟨19,by decide⟩).lower)
        (by norm_num [cell13054]) (by norm_num [cell13054])
      exact ⟨E.1,E.2.trans (by norm_num [cell13054])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy20 (n := 13054) (by norm_num)
        (q := 1 - (cell13054 ⟨20,by decide⟩).lower)
        (by norm_num [cell13054]) (by norm_num [cell13054])
      exact ⟨E.1,E.2.trans (by norm_num [cell13054])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy21 (n := 13054) (by norm_num)
        (q := 1 - (cell13054 ⟨21,by decide⟩).lower)
        (by norm_num [cell13054]) (by norm_num [cell13054])
      exact ⟨E.1,E.2.trans (by norm_num [cell13054])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy22 (n := 13054) (by norm_num)
        (q := 1 - (cell13054 ⟨22,by decide⟩).lower)
        (by norm_num [cell13054]) (by norm_num [cell13054])
      exact ⟨E.1,E.2.trans (by norm_num [cell13054])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy23 (n := 13054) (by norm_num)
        (q := 1 - (cell13054 ⟨23,by decide⟩).lower)
        (by norm_num [cell13054]) (by norm_num [cell13054])
      exact ⟨E.1,E.2.trans (by norm_num [cell13054])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy24 (n := 13054) (by norm_num)
        (q := 1 - (cell13054 ⟨24,by decide⟩).lower)
        (by norm_num [cell13054]) (by norm_num [cell13054])
      exact ⟨E.1,E.2.trans (by norm_num [cell13054])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy25 (n := 13054) (by norm_num)
        (q := 1 - (cell13054 ⟨25,by decide⟩).lower)
        (by norm_num [cell13054]) (by norm_num [cell13054])
      exact ⟨E.1,E.2.trans (by norm_num [cell13054])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy26 (n := 13054) (by norm_num)
        (q := 1 - (cell13054 ⟨26,by decide⟩).lower)
        (by norm_num [cell13054]) (by norm_num [cell13054])
      exact ⟨E.1,E.2.trans (by norm_num [cell13054])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy27 (n := 13054) (by norm_num)
        (q := 1 - (cell13054 ⟨27,by decide⟩).lower)
        (by norm_num [cell13054]) (by norm_num [cell13054])
      exact ⟨E.1,E.2.trans (by norm_num [cell13054])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy28 (n := 13054) (by norm_num)
        (q := 1 - (cell13054 ⟨28,by decide⟩).lower)
        (by norm_num [cell13054]) (by norm_num [cell13054])
      exact ⟨E.1,E.2.trans (by norm_num [cell13054])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy29 (n := 13054) (by norm_num)
        (q := 1 - (cell13054 ⟨29,by decide⟩).lower)
        (by norm_num [cell13054]) (by norm_num [cell13054])
      exact ⟨E.1,E.2.trans (by norm_num [cell13054])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy30 (n := 13054) (by norm_num)
        (q := 1 - (cell13054 ⟨30,by decide⟩).lower)
        (by norm_num [cell13054]) (by norm_num [cell13054])
      exact ⟨E.1,E.2.trans (by norm_num [cell13054])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy31 (n := 13054) (by norm_num)
        (q := 1 - (cell13054 ⟨31,by decide⟩).lower)
        (by norm_num [cell13054]) (by norm_num [cell13054])
      exact ⟨E.1,E.2.trans (by norm_num [cell13054])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy32 (n := 13054) (by norm_num)
        (q := 1 - (cell13054 ⟨32,by decide⟩).lower)
        (by norm_num [cell13054]) (by norm_num [cell13054])
      exact ⟨E.1,E.2.trans (by norm_num [cell13054])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy33 (n := 13054) (by norm_num)
        (q := 1 - (cell13054 ⟨33,by decide⟩).lower)
        (by norm_num [cell13054]) (by norm_num [cell13054])
      exact ⟨E.1,E.2.trans (by norm_num [cell13054])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy34 (n := 13054) (by norm_num)
        (q := 1 - (cell13054 ⟨34,by decide⟩).lower)
        (by norm_num [cell13054]) (by norm_num [cell13054])
      exact ⟨E.1,E.2.trans (by norm_num [cell13054])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy35 (n := 13054) (by norm_num)
        (q := 1 - (cell13054 ⟨35,by decide⟩).lower)
        (by norm_num [cell13054]) (by norm_num [cell13054])
      exact ⟨E.1,E.2.trans (by norm_num [cell13054])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy36 (n := 13054) (by norm_num)
        (q := 1 - (cell13054 ⟨36,by decide⟩).lower)
        (by norm_num [cell13054]) (by norm_num [cell13054])
      exact ⟨E.1,E.2.trans (by norm_num [cell13054])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy37 (n := 13054) (by norm_num)
        (q := 1 - (cell13054 ⟨37,by decide⟩).lower)
        (by norm_num [cell13054]) (by norm_num [cell13054])
      exact ⟨E.1,E.2.trans (by norm_num [cell13054])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy38 (n := 13054) (by norm_num)
        (q := 1 - (cell13054 ⟨38,by decide⟩).lower)
        (by norm_num [cell13054]) (by norm_num [cell13054])
      exact ⟨E.1,E.2.trans (by norm_num [cell13054])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy39 (n := 13054) (by norm_num)
        (q := 1 - (cell13054 ⟨39,by decide⟩).lower)
        (by norm_num [cell13054]) (by norm_num [cell13054])
      exact ⟨E.1,E.2.trans (by norm_num [cell13054])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy40 (n := 13054) (by norm_num)
        (q := 1 - (cell13054 ⟨40,by decide⟩).lower)
        (by norm_num [cell13054]) (by norm_num [cell13054])
      exact ⟨E.1,E.2.trans (by norm_num [cell13054])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy41 (n := 13054) (by norm_num)
        (q := 1 - (cell13054 ⟨41,by decide⟩).lower)
        (by norm_num [cell13054]) (by norm_num [cell13054])
      exact ⟨E.1,E.2.trans (by norm_num [cell13054])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy42 (n := 13054) (by norm_num)
        (q := 1 - (cell13054 ⟨42,by decide⟩).lower)
        (by norm_num [cell13054]) (by norm_num [cell13054])
      exact ⟨E.1,E.2.trans (by norm_num [cell13054])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy43 (n := 13054) (by norm_num)
        (q := 1 - (cell13054 ⟨43,by decide⟩).lower)
        (by norm_num [cell13054]) (by norm_num [cell13054])
      exact ⟨E.1,E.2.trans (by norm_num [cell13054])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy44 (n := 13054) (by norm_num)
        (q := 1 - (cell13054 ⟨44,by decide⟩).lower)
        (by norm_num [cell13054]) (by norm_num [cell13054])
      exact ⟨E.1,E.2.trans (by norm_num [cell13054])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy45 (n := 13054) (by norm_num)
        (q := 1 - (cell13054 ⟨45,by decide⟩).lower)
        (by norm_num [cell13054]) (by norm_num [cell13054])
      exact ⟨E.1,E.2.trans (by norm_num [cell13054])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy46 (n := 13054) (by norm_num)
        (q := 1 - (cell13054 ⟨46,by decide⟩).lower)
        (by norm_num [cell13054]) (by norm_num [cell13054])
      exact ⟨E.1,E.2.trans (by norm_num [cell13054])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy47 (n := 13054) (by norm_num)
        (q := 1 - (cell13054 ⟨47,by decide⟩).lower)
        (by norm_num [cell13054]) (by norm_num [cell13054])
      exact ⟨E.1,E.2.trans (by norm_num [cell13054])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy48 (n := 13054) (by norm_num)
        (q := 1 - (cell13054 ⟨48,by decide⟩).lower)
        (by norm_num [cell13054]) (by norm_num [cell13054])
      exact ⟨E.1,E.2.trans (by norm_num [cell13054])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy49 (n := 13054) (by norm_num)
        (q := 1 - (cell13054 ⟨49,by decide⟩).lower)
        (by norm_num [cell13054]) (by norm_num [cell13054])
      exact ⟨E.1,E.2.trans (by norm_num [cell13054])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy50 (n := 13054) (by norm_num)
        (q := 1 - (cell13054 ⟨50,by decide⟩).lower)
        (by norm_num [cell13054]) (by norm_num [cell13054])
      exact ⟨E.1,E.2.trans (by norm_num [cell13054])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy51 (n := 13054) (by norm_num)
        (q := 1 - (cell13054 ⟨51,by decide⟩).lower)
        (by norm_num [cell13054]) (by norm_num [cell13054])
      exact ⟨E.1,E.2.trans (by norm_num [cell13054])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy52 (n := 13054) (by norm_num)
        (q := 1 - (cell13054 ⟨52,by decide⟩).lower)
        (by norm_num [cell13054]) (by norm_num [cell13054])
      exact ⟨E.1,E.2.trans (by norm_num [cell13054])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13054

/-! Source-cell containment and simple scalar guards at 13054. -/
namespace BstLean.Part269.N13054
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13054)
open BstLean.Part268 (cell13054)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13054 ⟨10,by decide⟩).lower ∧ (cell13054 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13054 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13054 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13054 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13054 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13054 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13054,cell13054,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13054 ⟨11,by decide⟩).lower ∧ (cell13054 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13054 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13054 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13054 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13054 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13054 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13054,cell13054,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13054 ⟨12,by decide⟩).lower ∧ (cell13054 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13054 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13054 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13054 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13054 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13054 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13054,cell13054,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13054 ⟨13,by decide⟩).lower ∧ (cell13054 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13054 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13054 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13054 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13054 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13054 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13054,cell13054,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13054 ⟨14,by decide⟩).lower ∧ (cell13054 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13054 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13054 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13054 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13054 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13054 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13054,cell13054,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13054 ⟨15,by decide⟩).lower ∧ (cell13054 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13054 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13054 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13054 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13054 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13054 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13054,cell13054,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13054 ⟨16,by decide⟩).lower ∧ (cell13054 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13054 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13054 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13054 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13054 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13054 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13054,cell13054,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13054 ⟨17,by decide⟩).lower ∧ (cell13054 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13054 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13054 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13054 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13054 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13054 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13054,cell13054,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13054 ⟨18,by decide⟩).lower ∧ (cell13054 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13054 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13054 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13054 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13054 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13054 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13054,cell13054,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13054 ⟨19,by decide⟩).lower ∧ (cell13054 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13054 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13054 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13054 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13054 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13054 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13054,cell13054,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13054 ⟨20,by decide⟩).lower ∧ (cell13054 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13054 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13054 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13054 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13054 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13054 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13054,cell13054,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13054 ⟨21,by decide⟩).lower ∧ (cell13054 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13054 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13054 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13054 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13054 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13054 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13054,cell13054,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13054 ⟨22,by decide⟩).lower ∧ (cell13054 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13054 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13054 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13054 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13054 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13054 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13054,cell13054,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13054 ⟨23,by decide⟩).lower ∧ (cell13054 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13054 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13054 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13054 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13054 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13054 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13054,cell13054,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13054 ⟨24,by decide⟩).lower ∧ (cell13054 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13054 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13054 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13054 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13054 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13054 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13054,cell13054,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13054 ⟨25,by decide⟩).lower ∧ (cell13054 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13054 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13054 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13054 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13054 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13054 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13054,cell13054,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13054 ⟨26,by decide⟩).lower ∧ (cell13054 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13054 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13054 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13054 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13054 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13054 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13054,cell13054,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13054 ⟨27,by decide⟩).lower ∧ (cell13054 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13054 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13054 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13054 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13054 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13054 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13054,cell13054,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13054 ⟨28,by decide⟩).lower ∧ (cell13054 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13054 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13054 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13054 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13054 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13054 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13054,cell13054,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13054 ⟨29,by decide⟩).lower ∧ (cell13054 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13054 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13054 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13054 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13054 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13054 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13054,cell13054,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13054 ⟨30,by decide⟩).lower ∧ (cell13054 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13054 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13054 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13054 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13054 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13054 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13054,cell13054,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13054 ⟨31,by decide⟩).lower ∧ (cell13054 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13054 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13054 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13054 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13054 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13054 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13054,cell13054,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13054 ⟨32,by decide⟩).lower ∧ (cell13054 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13054 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13054 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13054 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13054 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13054 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13054,cell13054,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13054 ⟨33,by decide⟩).lower ∧ (cell13054 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13054 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13054 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13054 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13054 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13054 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13054,cell13054,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13054 ⟨34,by decide⟩).lower ∧ (cell13054 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13054 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13054 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13054 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13054 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13054 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13054,cell13054,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13054 ⟨35,by decide⟩).lower ∧ (cell13054 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13054 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13054 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13054 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13054 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13054 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13054,cell13054,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13054 ⟨36,by decide⟩).lower ∧ (cell13054 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13054 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13054 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13054 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13054 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13054 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13054,cell13054,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13054 ⟨37,by decide⟩).lower ∧ (cell13054 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13054 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13054 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13054 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13054 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13054 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13054,cell13054,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13054 ⟨38,by decide⟩).lower ∧ (cell13054 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13054 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13054 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13054 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13054 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13054 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13054,cell13054,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13054 ⟨39,by decide⟩).lower ∧ (cell13054 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13054 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13054 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13054 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13054 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13054 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13054,cell13054,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13054 ⟨40,by decide⟩).lower ∧ (cell13054 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13054 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13054 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13054 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13054 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13054 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13054,cell13054,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13054 ⟨41,by decide⟩).lower ∧ (cell13054 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13054 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13054 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13054 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13054 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13054 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13054,cell13054,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13054 ⟨42,by decide⟩).lower ∧ (cell13054 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13054 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13054 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13054 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13054 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13054 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13054,cell13054,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13054 ⟨43,by decide⟩).lower ∧ (cell13054 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13054 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13054 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13054 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13054 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13054 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13054,cell13054,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13054 ⟨44,by decide⟩).lower ∧ (cell13054 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13054 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13054 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13054 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13054 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13054 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13054,cell13054,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13054 ⟨45,by decide⟩).lower ∧ (cell13054 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13054 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13054 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13054 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13054 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13054 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13054,cell13054,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13054 ⟨46,by decide⟩).lower ∧ (cell13054 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13054 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13054 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13054 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13054 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13054 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13054,cell13054,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13054 ⟨47,by decide⟩).lower ∧ (cell13054 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13054 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13054 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13054 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13054 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13054 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13054,cell13054,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13054 ⟨48,by decide⟩).lower ∧ (cell13054 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13054 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13054 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13054 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13054 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13054 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13054,cell13054,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13054 ⟨49,by decide⟩).lower ∧ (cell13054 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13054 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13054 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13054 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13054 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13054 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13054,cell13054,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13054 ⟨50,by decide⟩).lower ∧ (cell13054 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13054 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13054 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13054 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13054 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13054 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13054,cell13054,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13054 ⟨51,by decide⟩).lower ∧ (cell13054 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13054 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13054 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13054 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13054 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13054 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13054,cell13054,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13054 ⟨52,by decide⟩).lower ∧ (cell13054 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13054 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13054 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13054 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13054 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13054 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13054,cell13054,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13054 i).lower ∧
    (cell13054 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13054 i).upper ≤ (0.532 : ℝ) ∧
    (cell13054 i).centre ≤ (0.1 : ℝ) ∧ (cell13054 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13054 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13054 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13054

/-! The local source numeric instances at 13054 have no network premises. -/
namespace BstLean.Part269.N13054
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13054)
open BstLean.Part268 (cell13054)

noncomputable def sourceNumerics13054 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13054 (cell13054 i)
      scalarRow13054.M scalarRow13054.H scalarRow13054.xi := by
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
    energy_allowance := scalarRow13054.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13054]
    centre_nonneg := (scalarRow13054.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D28.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13054])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13054
/-! Actual 13055 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13055
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13055 ≤ (1.035314738843 : ℝ) := by
  have hr : (114.258478897629 : ℝ) ≤ √(13055 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.258478897629 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13055 13055 (11 / 1000) ≤
    (0.008366004330 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13055) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.258478897629 : ℝ) ≤ √(13055 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13055)
  have hdiv : K / √(13055 : ℝ) ≤ K / 114.258478897629 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.258478897629 ≤ (0.008366004330 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13055.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13055 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13055 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13055 := gPlus_lower 13055
end BstLean.Part269.N13055

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13055
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035314738842 : ℝ) ≤ wn 13055 := by
  have hn : √(13055 : ℝ) ≤ 114.258478897630 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13055 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.258478897630 ≤ 2 / √(13055 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000244914587 : ℝ) ≤ rhoBar 13055 BstLean.Part154.csC ∧
    rhoBar 13055 BstLean.Part154.csC ≤ 0.000244914966 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035314738842 : ℝ) / (1.295212 * 13055) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035314738843 : ℝ) / (1.29521 * 13055) := by gcongr
      _ ≤ (0.000244914966 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13055 BstLean.Part154.csC) ≤ 0.000979719848 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13055 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13055 BstLean.Part154.csC) (piBar (rhoBar 13055 BstLean.Part154.csC)) ≤ 0.000187067463 ∧
    cc1 (rhoBar 13055 BstLean.Part154.csC) (piBar (rhoBar 13055 BstLean.Part154.csC)) ≤ 0.000119032318 ∧
    cc2 (rhoBar 13055 BstLean.Part154.csC) ≤ 0.000069099233 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13055 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13055 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13055 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13055 BstLean.Part154.csC * nuR (rhoBar 13055 BstLean.Part154.csC)) ≤ 0.000489844928 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000244914966 : ℝ) * 0.000979719848 := by gcongr
      _ ≤ (0.000489844928 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13055 BstLean.Part154.csC) * nuR (rhoBar 13055 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000979719848 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13055 BstLean.Part154.csC) * rhoBar 13055 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000244914966 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000244914966 / 2 + 0.399 * 0.000979719848 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000187067463 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000489844928 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119032318 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000244914966 / 1.414213562 := by gcongr
      _ ≤ (0.000069099233 : ℝ) := by norm_num

end BstLean.Part269.N13055

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13055
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13055 BstLean.Part154.csC) (piBar (rhoBar 13055 BstLean.Part154.csC)) ≤ 1.51124E-7 := by
  have hr0 : 0 ≤ rhoBar 13055 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13055 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13055 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13055 BstLean.Part154.csC) (piBar (rhoBar 13055 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13055 BstLean.Part154.csC) (piBar (rhoBar 13055 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13055 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000187067463 : ℝ) ^ 2 + 0.000119032318 ^ 2 + 3 * 0.000069099233 ^ 2 +
        2 * 0.797885 * 0.000187067463 * 0.000119032318 + 2 * 0.000187067463 * 0.000069099233 +
        4 * 0.797885 * 0.000119032318 * 0.000069099233 := by gcongr
    _ ≤ (1.51124E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13055 BstLean.Part154.csC Θ ≤ 0.002555354608 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13055 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13055 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13055 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13055 BstLean.Part154.csC) (piBar (rhoBar 13055 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13055 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035314738843 * 1.51124E-7 / (0.000244914587 : ℝ) := by gcongr
    _ ≤ 0.002555354608 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13055 BstLean.Part154.csC Θ ≤ 0.002833940394 + 0.000645695747 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13055 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13055 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13055 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035314738843 : ℝ) * ((2 * Θ * 0.000244914966 +
        (6863 / 10000) * 0.000244914966 * 13055 * 0.000979719848) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002833940394 + 0.000645695747 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13055 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13055 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13055 0.011 Θ ∧ gammaRatio 13055 0.011 Θ ≤ 0.000084195432 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13055 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035314738843 : ℝ) * 0.525 / ((1 - 0.011) * 13055) := by gcongr
      _ ≤ (0.000084195432 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13055 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13055 0.011 Θ) :=
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
    badAllowance 13055 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000383749387 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13055 BstLean.Part154.csC) 1.22 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 2 (rhoBar 13055 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13055 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13055 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13055 0.011 Θ) 1.12 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 1 (gammaRatio 13055 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13055 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13055 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13055 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13055 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035314738843 : ℝ) * 13055 *
        (1.3781E-8 / 1.1045361 + 1.6832E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000383749387 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13055 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003217689781 + 0.003201050355 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13055

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13055
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13055 BstLean.Part154.csC) (piBar (rhoBar 13055 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13055 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13055 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13055 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13055 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13055 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13055 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13055 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13055 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13055 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13055 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13055 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13055 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13055 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13055 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051758116393 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13055) ≤ 0.010452069664 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13055 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035314738843)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010452069664 + 2 * 0.737676 / 13055) := by gcongr
    _ ≤ (0.051758116393 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13055 12 ≤ 0.0015 := by
  exact BstLean.Part269.S28.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13055

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13055
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560519185890 : ℝ) ≤ plow 13055 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13055) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052404841218)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001341561170) : eMP 13055 0.011 xi bn ≤ 0.001155428447 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13055 : ℝ) * (1 - 0.011))) ≤ 0.000571338666 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001341561170 / (13055 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000571338666 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000571338666 : ℝ) + 3.141593 * 0.052404841218 / (13055 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001155428447 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052404841218)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001341561170) : PiBarMP 13055 12 0.011 xi bn ≤ 0.159021838798 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13055 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036627328186 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.628319533468 : ℝ) ≤ √((13055 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.258478897629 : ℝ) ≤ √(13055 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13055) ≤ 0.121937631213 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036627328186 + 0.052404841218 * 1.772454 / (2 * (113.628319533468 : ℝ))) * (1 + 0.001155428447) +
        8 / (13055 * 114.258478897629) + 0.121937631213 := by gcongr
    _ ≤ (0.159021838798 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052404841218)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001341561170) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280679153474) :
    parallelOracle 13055 0.011 xi bn cd ≤ 0.159985354258 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13055 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13055 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560519185890 : ℝ) ≤ plow 13055 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.258478897629 : ℝ) ≤ √(13055 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280679153474 : ℝ) / (2 * 0.560519185890 * 114.258478897629)) * 0.159021838798 +
        0.280679153474 ^ 2 / (2 * 0.560519185890 * 114.258478897629) := by gcongr
    _ ≤ (0.159985354258 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052404841218) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001341561170)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280679153474) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13055 13055 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560519185890 : ℝ) ≤ plow 13055 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.258478897629 : ℝ) ≤ √(13055 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13055 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13055 Θ 1.22 ≤ 0.011606145232 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.258478897629 := by gcongr <;> linarith
      _ ≤ (0.011606145232 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13055 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13055 13055 0.011 ≤ 0.008366004330 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13055 13055 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13055 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13055 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13055 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13055 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159985354258 + 0.011606145232 + (0.008366004330 : ℝ) *
        (1 + 2 * (0.280679153474 + 0.011606145232) / (0.560519185890 * 114.258478897629))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13055]

end BstLean.Part269.N13055

/-! The original eight local profiles supply actual 13055 moment certificates. -/
namespace BstLean.Part269.N13055
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13055 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13055 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13055 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052404841218 ∧
    0 ≤ bN 13055 BstLean.Part154.csC (groupTheta g) ∧ bN 13055 BstLean.Part154.csC (groupTheta g) ≤ 0.001341561170 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13055 13055 0.011
      (momentAllowance 13055 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13055 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13055 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13055 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13055 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13055 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228921037081 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13055 0.011
      (momentAllowance 13055 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13055 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13055
/-! The actual computed-centre upper energy formula at 13055. -/
namespace BstLean.Part269.N13055
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13055

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13055
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13055)
open BstLean.Part268 (cell13055)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084517292137
  | 2 => 0.085444106720
  | 3 => 0.086366851212
  | 4 => 0.087286424356
  | 5 => 0.088203928308
  | 6 => 0.089120700701
  | 7 => 0.090038350094
  | 8 => 0.090958794882
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13055 13055 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13055 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003218831707 + 0.003202305177 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S28.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13055

/-! Actual upper energy certificates on all 43 source endpoints at 13055. -/
namespace BstLean.Part269.N13055
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13055)
open BstLean.Part268 (cell13055)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13055 (gMinus 13055) (1 - (cell13055 i).lower) ≤ 1 ∧
    energyUpper 13055 (gMinus 13055) (BstLean.Part211.gPlus 13055)
      (finiteEnergy 13055 13055 0.011) (1 - (cell13055 i).lower) ≤
      (cell13055 i).energy := by
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
      have E := BstLean.Part269.S28.uniformEnergy10 (n := 13055) (by norm_num)
        (q := 1 - (cell13055 ⟨10,by decide⟩).lower)
        (by norm_num [cell13055]) (by norm_num [cell13055])
      exact ⟨E.1,E.2.trans (by norm_num [cell13055])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy11 (n := 13055) (by norm_num)
        (q := 1 - (cell13055 ⟨11,by decide⟩).lower)
        (by norm_num [cell13055]) (by norm_num [cell13055])
      exact ⟨E.1,E.2.trans (by norm_num [cell13055])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy12 (n := 13055) (by norm_num)
        (q := 1 - (cell13055 ⟨12,by decide⟩).lower)
        (by norm_num [cell13055]) (by norm_num [cell13055])
      exact ⟨E.1,E.2.trans (by norm_num [cell13055])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy13 (n := 13055) (by norm_num)
        (q := 1 - (cell13055 ⟨13,by decide⟩).lower)
        (by norm_num [cell13055]) (by norm_num [cell13055])
      exact ⟨E.1,E.2.trans (by norm_num [cell13055])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy14 (n := 13055) (by norm_num)
        (q := 1 - (cell13055 ⟨14,by decide⟩).lower)
        (by norm_num [cell13055]) (by norm_num [cell13055])
      exact ⟨E.1,E.2.trans (by norm_num [cell13055])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy15 (n := 13055) (by norm_num)
        (q := 1 - (cell13055 ⟨15,by decide⟩).lower)
        (by norm_num [cell13055]) (by norm_num [cell13055])
      exact ⟨E.1,E.2.trans (by norm_num [cell13055])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy16 (n := 13055) (by norm_num)
        (q := 1 - (cell13055 ⟨16,by decide⟩).lower)
        (by norm_num [cell13055]) (by norm_num [cell13055])
      exact ⟨E.1,E.2.trans (by norm_num [cell13055])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy17 (n := 13055) (by norm_num)
        (q := 1 - (cell13055 ⟨17,by decide⟩).lower)
        (by norm_num [cell13055]) (by norm_num [cell13055])
      exact ⟨E.1,E.2.trans (by norm_num [cell13055])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy18 (n := 13055) (by norm_num)
        (q := 1 - (cell13055 ⟨18,by decide⟩).lower)
        (by norm_num [cell13055]) (by norm_num [cell13055])
      exact ⟨E.1,E.2.trans (by norm_num [cell13055])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy19 (n := 13055) (by norm_num)
        (q := 1 - (cell13055 ⟨19,by decide⟩).lower)
        (by norm_num [cell13055]) (by norm_num [cell13055])
      exact ⟨E.1,E.2.trans (by norm_num [cell13055])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy20 (n := 13055) (by norm_num)
        (q := 1 - (cell13055 ⟨20,by decide⟩).lower)
        (by norm_num [cell13055]) (by norm_num [cell13055])
      exact ⟨E.1,E.2.trans (by norm_num [cell13055])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy21 (n := 13055) (by norm_num)
        (q := 1 - (cell13055 ⟨21,by decide⟩).lower)
        (by norm_num [cell13055]) (by norm_num [cell13055])
      exact ⟨E.1,E.2.trans (by norm_num [cell13055])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy22 (n := 13055) (by norm_num)
        (q := 1 - (cell13055 ⟨22,by decide⟩).lower)
        (by norm_num [cell13055]) (by norm_num [cell13055])
      exact ⟨E.1,E.2.trans (by norm_num [cell13055])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy23 (n := 13055) (by norm_num)
        (q := 1 - (cell13055 ⟨23,by decide⟩).lower)
        (by norm_num [cell13055]) (by norm_num [cell13055])
      exact ⟨E.1,E.2.trans (by norm_num [cell13055])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy24 (n := 13055) (by norm_num)
        (q := 1 - (cell13055 ⟨24,by decide⟩).lower)
        (by norm_num [cell13055]) (by norm_num [cell13055])
      exact ⟨E.1,E.2.trans (by norm_num [cell13055])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy25 (n := 13055) (by norm_num)
        (q := 1 - (cell13055 ⟨25,by decide⟩).lower)
        (by norm_num [cell13055]) (by norm_num [cell13055])
      exact ⟨E.1,E.2.trans (by norm_num [cell13055])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy26 (n := 13055) (by norm_num)
        (q := 1 - (cell13055 ⟨26,by decide⟩).lower)
        (by norm_num [cell13055]) (by norm_num [cell13055])
      exact ⟨E.1,E.2.trans (by norm_num [cell13055])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy27 (n := 13055) (by norm_num)
        (q := 1 - (cell13055 ⟨27,by decide⟩).lower)
        (by norm_num [cell13055]) (by norm_num [cell13055])
      exact ⟨E.1,E.2.trans (by norm_num [cell13055])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy28 (n := 13055) (by norm_num)
        (q := 1 - (cell13055 ⟨28,by decide⟩).lower)
        (by norm_num [cell13055]) (by norm_num [cell13055])
      exact ⟨E.1,E.2.trans (by norm_num [cell13055])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy29 (n := 13055) (by norm_num)
        (q := 1 - (cell13055 ⟨29,by decide⟩).lower)
        (by norm_num [cell13055]) (by norm_num [cell13055])
      exact ⟨E.1,E.2.trans (by norm_num [cell13055])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy30 (n := 13055) (by norm_num)
        (q := 1 - (cell13055 ⟨30,by decide⟩).lower)
        (by norm_num [cell13055]) (by norm_num [cell13055])
      exact ⟨E.1,E.2.trans (by norm_num [cell13055])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy31 (n := 13055) (by norm_num)
        (q := 1 - (cell13055 ⟨31,by decide⟩).lower)
        (by norm_num [cell13055]) (by norm_num [cell13055])
      exact ⟨E.1,E.2.trans (by norm_num [cell13055])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy32 (n := 13055) (by norm_num)
        (q := 1 - (cell13055 ⟨32,by decide⟩).lower)
        (by norm_num [cell13055]) (by norm_num [cell13055])
      exact ⟨E.1,E.2.trans (by norm_num [cell13055])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy33 (n := 13055) (by norm_num)
        (q := 1 - (cell13055 ⟨33,by decide⟩).lower)
        (by norm_num [cell13055]) (by norm_num [cell13055])
      exact ⟨E.1,E.2.trans (by norm_num [cell13055])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy34 (n := 13055) (by norm_num)
        (q := 1 - (cell13055 ⟨34,by decide⟩).lower)
        (by norm_num [cell13055]) (by norm_num [cell13055])
      exact ⟨E.1,E.2.trans (by norm_num [cell13055])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy35 (n := 13055) (by norm_num)
        (q := 1 - (cell13055 ⟨35,by decide⟩).lower)
        (by norm_num [cell13055]) (by norm_num [cell13055])
      exact ⟨E.1,E.2.trans (by norm_num [cell13055])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy36 (n := 13055) (by norm_num)
        (q := 1 - (cell13055 ⟨36,by decide⟩).lower)
        (by norm_num [cell13055]) (by norm_num [cell13055])
      exact ⟨E.1,E.2.trans (by norm_num [cell13055])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy37 (n := 13055) (by norm_num)
        (q := 1 - (cell13055 ⟨37,by decide⟩).lower)
        (by norm_num [cell13055]) (by norm_num [cell13055])
      exact ⟨E.1,E.2.trans (by norm_num [cell13055])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy38 (n := 13055) (by norm_num)
        (q := 1 - (cell13055 ⟨38,by decide⟩).lower)
        (by norm_num [cell13055]) (by norm_num [cell13055])
      exact ⟨E.1,E.2.trans (by norm_num [cell13055])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy39 (n := 13055) (by norm_num)
        (q := 1 - (cell13055 ⟨39,by decide⟩).lower)
        (by norm_num [cell13055]) (by norm_num [cell13055])
      exact ⟨E.1,E.2.trans (by norm_num [cell13055])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy40 (n := 13055) (by norm_num)
        (q := 1 - (cell13055 ⟨40,by decide⟩).lower)
        (by norm_num [cell13055]) (by norm_num [cell13055])
      exact ⟨E.1,E.2.trans (by norm_num [cell13055])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy41 (n := 13055) (by norm_num)
        (q := 1 - (cell13055 ⟨41,by decide⟩).lower)
        (by norm_num [cell13055]) (by norm_num [cell13055])
      exact ⟨E.1,E.2.trans (by norm_num [cell13055])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy42 (n := 13055) (by norm_num)
        (q := 1 - (cell13055 ⟨42,by decide⟩).lower)
        (by norm_num [cell13055]) (by norm_num [cell13055])
      exact ⟨E.1,E.2.trans (by norm_num [cell13055])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy43 (n := 13055) (by norm_num)
        (q := 1 - (cell13055 ⟨43,by decide⟩).lower)
        (by norm_num [cell13055]) (by norm_num [cell13055])
      exact ⟨E.1,E.2.trans (by norm_num [cell13055])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy44 (n := 13055) (by norm_num)
        (q := 1 - (cell13055 ⟨44,by decide⟩).lower)
        (by norm_num [cell13055]) (by norm_num [cell13055])
      exact ⟨E.1,E.2.trans (by norm_num [cell13055])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy45 (n := 13055) (by norm_num)
        (q := 1 - (cell13055 ⟨45,by decide⟩).lower)
        (by norm_num [cell13055]) (by norm_num [cell13055])
      exact ⟨E.1,E.2.trans (by norm_num [cell13055])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy46 (n := 13055) (by norm_num)
        (q := 1 - (cell13055 ⟨46,by decide⟩).lower)
        (by norm_num [cell13055]) (by norm_num [cell13055])
      exact ⟨E.1,E.2.trans (by norm_num [cell13055])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy47 (n := 13055) (by norm_num)
        (q := 1 - (cell13055 ⟨47,by decide⟩).lower)
        (by norm_num [cell13055]) (by norm_num [cell13055])
      exact ⟨E.1,E.2.trans (by norm_num [cell13055])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy48 (n := 13055) (by norm_num)
        (q := 1 - (cell13055 ⟨48,by decide⟩).lower)
        (by norm_num [cell13055]) (by norm_num [cell13055])
      exact ⟨E.1,E.2.trans (by norm_num [cell13055])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy49 (n := 13055) (by norm_num)
        (q := 1 - (cell13055 ⟨49,by decide⟩).lower)
        (by norm_num [cell13055]) (by norm_num [cell13055])
      exact ⟨E.1,E.2.trans (by norm_num [cell13055])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy50 (n := 13055) (by norm_num)
        (q := 1 - (cell13055 ⟨50,by decide⟩).lower)
        (by norm_num [cell13055]) (by norm_num [cell13055])
      exact ⟨E.1,E.2.trans (by norm_num [cell13055])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy51 (n := 13055) (by norm_num)
        (q := 1 - (cell13055 ⟨51,by decide⟩).lower)
        (by norm_num [cell13055]) (by norm_num [cell13055])
      exact ⟨E.1,E.2.trans (by norm_num [cell13055])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy52 (n := 13055) (by norm_num)
        (q := 1 - (cell13055 ⟨52,by decide⟩).lower)
        (by norm_num [cell13055]) (by norm_num [cell13055])
      exact ⟨E.1,E.2.trans (by norm_num [cell13055])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13055

/-! Source-cell containment and simple scalar guards at 13055. -/
namespace BstLean.Part269.N13055
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13055)
open BstLean.Part268 (cell13055)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13055 ⟨10,by decide⟩).lower ∧ (cell13055 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13055 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13055 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13055 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13055 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13055 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13055,cell13055,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13055 ⟨11,by decide⟩).lower ∧ (cell13055 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13055 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13055 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13055 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13055 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13055 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13055,cell13055,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13055 ⟨12,by decide⟩).lower ∧ (cell13055 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13055 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13055 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13055 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13055 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13055 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13055,cell13055,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13055 ⟨13,by decide⟩).lower ∧ (cell13055 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13055 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13055 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13055 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13055 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13055 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13055,cell13055,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13055 ⟨14,by decide⟩).lower ∧ (cell13055 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13055 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13055 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13055 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13055 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13055 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13055,cell13055,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13055 ⟨15,by decide⟩).lower ∧ (cell13055 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13055 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13055 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13055 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13055 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13055 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13055,cell13055,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13055 ⟨16,by decide⟩).lower ∧ (cell13055 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13055 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13055 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13055 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13055 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13055 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13055,cell13055,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13055 ⟨17,by decide⟩).lower ∧ (cell13055 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13055 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13055 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13055 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13055 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13055 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13055,cell13055,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13055 ⟨18,by decide⟩).lower ∧ (cell13055 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13055 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13055 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13055 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13055 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13055 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13055,cell13055,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13055 ⟨19,by decide⟩).lower ∧ (cell13055 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13055 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13055 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13055 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13055 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13055 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13055,cell13055,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13055 ⟨20,by decide⟩).lower ∧ (cell13055 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13055 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13055 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13055 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13055 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13055 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13055,cell13055,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13055 ⟨21,by decide⟩).lower ∧ (cell13055 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13055 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13055 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13055 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13055 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13055 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13055,cell13055,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13055 ⟨22,by decide⟩).lower ∧ (cell13055 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13055 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13055 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13055 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13055 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13055 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13055,cell13055,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13055 ⟨23,by decide⟩).lower ∧ (cell13055 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13055 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13055 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13055 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13055 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13055 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13055,cell13055,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13055 ⟨24,by decide⟩).lower ∧ (cell13055 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13055 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13055 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13055 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13055 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13055 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13055,cell13055,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13055 ⟨25,by decide⟩).lower ∧ (cell13055 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13055 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13055 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13055 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13055 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13055 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13055,cell13055,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13055 ⟨26,by decide⟩).lower ∧ (cell13055 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13055 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13055 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13055 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13055 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13055 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13055,cell13055,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13055 ⟨27,by decide⟩).lower ∧ (cell13055 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13055 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13055 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13055 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13055 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13055 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13055,cell13055,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13055 ⟨28,by decide⟩).lower ∧ (cell13055 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13055 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13055 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13055 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13055 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13055 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13055,cell13055,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13055 ⟨29,by decide⟩).lower ∧ (cell13055 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13055 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13055 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13055 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13055 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13055 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13055,cell13055,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13055 ⟨30,by decide⟩).lower ∧ (cell13055 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13055 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13055 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13055 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13055 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13055 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13055,cell13055,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13055 ⟨31,by decide⟩).lower ∧ (cell13055 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13055 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13055 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13055 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13055 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13055 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13055,cell13055,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13055 ⟨32,by decide⟩).lower ∧ (cell13055 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13055 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13055 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13055 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13055 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13055 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13055,cell13055,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13055 ⟨33,by decide⟩).lower ∧ (cell13055 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13055 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13055 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13055 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13055 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13055 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13055,cell13055,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13055 ⟨34,by decide⟩).lower ∧ (cell13055 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13055 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13055 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13055 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13055 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13055 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13055,cell13055,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13055 ⟨35,by decide⟩).lower ∧ (cell13055 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13055 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13055 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13055 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13055 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13055 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13055,cell13055,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13055 ⟨36,by decide⟩).lower ∧ (cell13055 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13055 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13055 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13055 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13055 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13055 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13055,cell13055,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13055 ⟨37,by decide⟩).lower ∧ (cell13055 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13055 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13055 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13055 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13055 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13055 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13055,cell13055,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13055 ⟨38,by decide⟩).lower ∧ (cell13055 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13055 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13055 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13055 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13055 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13055 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13055,cell13055,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13055 ⟨39,by decide⟩).lower ∧ (cell13055 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13055 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13055 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13055 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13055 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13055 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13055,cell13055,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13055 ⟨40,by decide⟩).lower ∧ (cell13055 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13055 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13055 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13055 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13055 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13055 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13055,cell13055,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13055 ⟨41,by decide⟩).lower ∧ (cell13055 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13055 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13055 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13055 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13055 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13055 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13055,cell13055,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13055 ⟨42,by decide⟩).lower ∧ (cell13055 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13055 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13055 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13055 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13055 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13055 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13055,cell13055,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13055 ⟨43,by decide⟩).lower ∧ (cell13055 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13055 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13055 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13055 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13055 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13055 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13055,cell13055,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13055 ⟨44,by decide⟩).lower ∧ (cell13055 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13055 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13055 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13055 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13055 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13055 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13055,cell13055,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13055 ⟨45,by decide⟩).lower ∧ (cell13055 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13055 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13055 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13055 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13055 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13055 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13055,cell13055,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13055 ⟨46,by decide⟩).lower ∧ (cell13055 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13055 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13055 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13055 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13055 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13055 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13055,cell13055,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13055 ⟨47,by decide⟩).lower ∧ (cell13055 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13055 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13055 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13055 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13055 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13055 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13055,cell13055,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13055 ⟨48,by decide⟩).lower ∧ (cell13055 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13055 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13055 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13055 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13055 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13055 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13055,cell13055,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13055 ⟨49,by decide⟩).lower ∧ (cell13055 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13055 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13055 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13055 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13055 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13055 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13055,cell13055,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13055 ⟨50,by decide⟩).lower ∧ (cell13055 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13055 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13055 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13055 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13055 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13055 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13055,cell13055,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13055 ⟨51,by decide⟩).lower ∧ (cell13055 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13055 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13055 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13055 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13055 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13055 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13055,cell13055,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13055 ⟨52,by decide⟩).lower ∧ (cell13055 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13055 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13055 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13055 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13055 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13055 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13055,cell13055,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13055 i).lower ∧
    (cell13055 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13055 i).upper ≤ (0.532 : ℝ) ∧
    (cell13055 i).centre ≤ (0.1 : ℝ) ∧ (cell13055 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13055 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13055 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13055

/-! The local source numeric instances at 13055 have no network premises. -/
namespace BstLean.Part269.N13055
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13055)
open BstLean.Part268 (cell13055)

noncomputable def sourceNumerics13055 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13055 (cell13055 i)
      scalarRow13055.M scalarRow13055.H scalarRow13055.xi := by
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
    energy_allowance := scalarRow13055.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13055]
    centre_nonneg := (scalarRow13055.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D28.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13055])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13055
/-! Actual 13056 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13056
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13056 ≤ (1.035313374650 : ℝ) := by
  have hr : (114.262854856685 : ℝ) ≤ √(13056 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.262854856685 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13056 13056 (11 / 1000) ≤
    (0.008365683932 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13056) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.262854856685 : ℝ) ≤ √(13056 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13056)
  have hdiv : K / √(13056 : ℝ) ≤ K / 114.262854856685 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.262854856685 ≤ (0.008365683932 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13056.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13056 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13056 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13056 := gPlus_lower 13056
end BstLean.Part269.N13056

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13056
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035313374649 : ℝ) ≤ wn 13056 := by
  have hn : √(13056 : ℝ) ≤ 114.262854856686 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13056 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.262854856686 ≤ 2 / √(13056 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000244895505 : ℝ) ≤ rhoBar 13056 BstLean.Part154.csC ∧
    rhoBar 13056 BstLean.Part154.csC ≤ 0.000244895884 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035313374649 : ℝ) / (1.295212 * 13056) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035313374650 : ℝ) / (1.29521 * 13056) := by gcongr
      _ ≤ (0.000244895884 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13056 BstLean.Part154.csC) ≤ 0.000979643510 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13056 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13056 BstLean.Part154.csC) (piBar (rhoBar 13056 BstLean.Part154.csC)) ≤ 0.000187052887 ∧
    cc1 (rhoBar 13056 BstLean.Part154.csC) (piBar (rhoBar 13056 BstLean.Part154.csC)) ≤ 0.000119023044 ∧
    cc2 (rhoBar 13056 BstLean.Part154.csC) ≤ 0.000069093849 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13056 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13056 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13056 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13056 BstLean.Part154.csC * nuR (rhoBar 13056 BstLean.Part154.csC)) ≤ 0.000489806762 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000244895884 : ℝ) * 0.000979643510 := by gcongr
      _ ≤ (0.000489806762 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13056 BstLean.Part154.csC) * nuR (rhoBar 13056 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000979643510 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13056 BstLean.Part154.csC) * rhoBar 13056 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000244895884 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000244895884 / 2 + 0.399 * 0.000979643510 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000187052887 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000489806762 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119023044 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000244895884 / 1.414213562 := by gcongr
      _ ≤ (0.000069093849 : ℝ) := by norm_num

end BstLean.Part269.N13056

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13056
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13056 BstLean.Part154.csC) (piBar (rhoBar 13056 BstLean.Part154.csC)) ≤ 1.51100E-7 := by
  have hr0 : 0 ≤ rhoBar 13056 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13056 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13056 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13056 BstLean.Part154.csC) (piBar (rhoBar 13056 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13056 BstLean.Part154.csC) (piBar (rhoBar 13056 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13056 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000187052887 : ℝ) ^ 2 + 0.000119023044 ^ 2 + 3 * 0.000069093849 ^ 2 +
        2 * 0.797885 * 0.000187052887 * 0.000119023044 + 2 * 0.000187052887 * 0.000069093849 +
        4 * 0.797885 * 0.000119023044 * 0.000069093849 := by gcongr
    _ ≤ (1.51100E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13056 BstLean.Part154.csC Θ ≤ 0.002555144504 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13056 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13056 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13056 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13056 BstLean.Part154.csC) (piBar (rhoBar 13056 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13056 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035313374650 * 1.51100E-7 / (0.000244895505 : ℝ) := by gcongr
    _ ≤ 0.002555144504 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13056 BstLean.Part154.csC Θ ≤ 0.002833712105 + 0.000645644589 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13056 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13056 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13056 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035313374650 : ℝ) * ((2 * Θ * 0.000244895884 +
        (6863 / 10000) * 0.000244895884 * 13056 * 0.000979643510) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002833712105 + 0.000645644589 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13056 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13056 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13056 0.011 Θ ∧ gammaRatio 13056 0.011 Θ ≤ 0.000084188872 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13056 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035313374650 : ℝ) * 0.525 / ((1 - 0.011) * 13056) := by gcongr
      _ ≤ (0.000084188872 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13056 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13056 0.011 Θ) :=
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
    badAllowance 13056 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000383749387 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13056 BstLean.Part154.csC) 1.22 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 2 (rhoBar 13056 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13056 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13056 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13056 0.011 Θ) 1.12 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 1 (gammaRatio 13056 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13056 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13056 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13056 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13056 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035313374650 : ℝ) * 13056 *
        (1.3781E-8 / 1.1045361 + 1.6832E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000383749387 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13056 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003217461492 + 0.003200789093 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13056

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13056
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13056 BstLean.Part154.csC) (piBar (rhoBar 13056 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13056 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13056 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13056 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13056 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13056 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13056 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13056 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13056 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13056 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13056 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13056 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13056 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13056 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13056 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051756112995 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13056) ≤ 0.010451669378 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13056 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035313374650)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010451669378 + 2 * 0.737676 / 13056) := by gcongr
    _ ≤ (0.051756112995 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13056 12 ≤ 0.0015 := by
  exact BstLean.Part269.S28.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13056

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13056
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560519228684 : ℝ) ≤ plow 13056 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13056) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052404475766)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001341450865) : eMP 13056 0.011 xi bn ≤ 0.001155336646 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13056 : ℝ) * (1 - 0.011))) ≤ 0.000571293298 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001341450865 / (13056 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000571293298 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000571293298 : ℝ) + 3.141593 * 0.052404475766 / (13056 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001155336646 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052404475766)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001341450865) : PiBarMP 13056 12 0.011 xi bn ≤ 0.159015638830 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13056 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036625822380 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.632671358196 : ℝ) ≤ √((13056 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.262854856685 : ℝ) ≤ √(13056 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13056) ≤ 0.121932961331 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036625822380 + 0.052404475766 * 1.772454 / (2 * (113.632671358196 : ℝ))) * (1 + 0.001155336646) +
        8 / (13056 * 114.262854856685) + 0.121932961331 := by gcongr
    _ ≤ (0.159015638830 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052404475766)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001341450865) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280676351869) :
    parallelOracle 13056 0.011 xi bn cd ≤ 0.159979087976 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13056 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13056 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560519228684 : ℝ) ≤ plow 13056 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.262854856685 : ℝ) ≤ √(13056 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280676351869 : ℝ) / (2 * 0.560519228684 * 114.262854856685)) * 0.159015638830 +
        0.280676351869 ^ 2 / (2 * 0.560519228684 * 114.262854856685) := by gcongr
    _ ≤ (0.159979087976 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052404475766) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001341450865)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280676351869) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13056 13056 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560519228684 : ℝ) ≤ plow 13056 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.262854856685 : ℝ) ≤ √(13056 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13056 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13056 Θ 1.22 ≤ 0.011605700748 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.262854856685 := by gcongr <;> linarith
      _ ≤ (0.011605700748 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13056 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13056 13056 0.011 ≤ 0.008365683932 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13056 13056 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13056 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13056 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13056 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13056 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159979087976 + 0.011605700748 + (0.008365683932 : ℝ) *
        (1 + 2 * (0.280676351869 + 0.011605700748) / (0.560519228684 * 114.262854856685))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13056]

end BstLean.Part269.N13056

/-! The original eight local profiles supply actual 13056 moment certificates. -/
namespace BstLean.Part269.N13056
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13056 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13056 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13056 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052404475766 ∧
    0 ≤ bN 13056 BstLean.Part154.csC (groupTheta g) ∧ bN 13056 BstLean.Part154.csC (groupTheta g) ≤ 0.001341450865 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13056 13056 0.011
      (momentAllowance 13056 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13056 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13056 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13056 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13056 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13056 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228920238874 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13056 0.011
      (momentAllowance 13056 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13056 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13056
/-! The actual computed-centre upper energy formula at 13056. -/
namespace BstLean.Part269.N13056
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13056

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13056
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13056)
open BstLean.Part268 (cell13056)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084514717219
  | 2 => 0.085441498769
  | 3 => 0.086364205336
  | 4 => 0.087283734510
  | 5 => 0.088201187079
  | 6 => 0.089117899069
  | 7 => 0.090035477160
  | 8 => 0.090955837568
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13056 13056 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13056 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003218831707 + 0.003202305177 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S28.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13056

/-! Actual upper energy certificates on all 43 source endpoints at 13056. -/
namespace BstLean.Part269.N13056
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13056)
open BstLean.Part268 (cell13056)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13056 (gMinus 13056) (1 - (cell13056 i).lower) ≤ 1 ∧
    energyUpper 13056 (gMinus 13056) (BstLean.Part211.gPlus 13056)
      (finiteEnergy 13056 13056 0.011) (1 - (cell13056 i).lower) ≤
      (cell13056 i).energy := by
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
      have E := BstLean.Part269.S28.uniformEnergy10 (n := 13056) (by norm_num)
        (q := 1 - (cell13056 ⟨10,by decide⟩).lower)
        (by norm_num [cell13056]) (by norm_num [cell13056])
      exact ⟨E.1,E.2.trans (by norm_num [cell13056])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy11 (n := 13056) (by norm_num)
        (q := 1 - (cell13056 ⟨11,by decide⟩).lower)
        (by norm_num [cell13056]) (by norm_num [cell13056])
      exact ⟨E.1,E.2.trans (by norm_num [cell13056])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy12 (n := 13056) (by norm_num)
        (q := 1 - (cell13056 ⟨12,by decide⟩).lower)
        (by norm_num [cell13056]) (by norm_num [cell13056])
      exact ⟨E.1,E.2.trans (by norm_num [cell13056])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy13 (n := 13056) (by norm_num)
        (q := 1 - (cell13056 ⟨13,by decide⟩).lower)
        (by norm_num [cell13056]) (by norm_num [cell13056])
      exact ⟨E.1,E.2.trans (by norm_num [cell13056])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy14 (n := 13056) (by norm_num)
        (q := 1 - (cell13056 ⟨14,by decide⟩).lower)
        (by norm_num [cell13056]) (by norm_num [cell13056])
      exact ⟨E.1,E.2.trans (by norm_num [cell13056])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy15 (n := 13056) (by norm_num)
        (q := 1 - (cell13056 ⟨15,by decide⟩).lower)
        (by norm_num [cell13056]) (by norm_num [cell13056])
      exact ⟨E.1,E.2.trans (by norm_num [cell13056])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy16 (n := 13056) (by norm_num)
        (q := 1 - (cell13056 ⟨16,by decide⟩).lower)
        (by norm_num [cell13056]) (by norm_num [cell13056])
      exact ⟨E.1,E.2.trans (by norm_num [cell13056])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy17 (n := 13056) (by norm_num)
        (q := 1 - (cell13056 ⟨17,by decide⟩).lower)
        (by norm_num [cell13056]) (by norm_num [cell13056])
      exact ⟨E.1,E.2.trans (by norm_num [cell13056])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy18 (n := 13056) (by norm_num)
        (q := 1 - (cell13056 ⟨18,by decide⟩).lower)
        (by norm_num [cell13056]) (by norm_num [cell13056])
      exact ⟨E.1,E.2.trans (by norm_num [cell13056])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy19 (n := 13056) (by norm_num)
        (q := 1 - (cell13056 ⟨19,by decide⟩).lower)
        (by norm_num [cell13056]) (by norm_num [cell13056])
      exact ⟨E.1,E.2.trans (by norm_num [cell13056])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy20 (n := 13056) (by norm_num)
        (q := 1 - (cell13056 ⟨20,by decide⟩).lower)
        (by norm_num [cell13056]) (by norm_num [cell13056])
      exact ⟨E.1,E.2.trans (by norm_num [cell13056])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy21 (n := 13056) (by norm_num)
        (q := 1 - (cell13056 ⟨21,by decide⟩).lower)
        (by norm_num [cell13056]) (by norm_num [cell13056])
      exact ⟨E.1,E.2.trans (by norm_num [cell13056])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy22 (n := 13056) (by norm_num)
        (q := 1 - (cell13056 ⟨22,by decide⟩).lower)
        (by norm_num [cell13056]) (by norm_num [cell13056])
      exact ⟨E.1,E.2.trans (by norm_num [cell13056])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy23 (n := 13056) (by norm_num)
        (q := 1 - (cell13056 ⟨23,by decide⟩).lower)
        (by norm_num [cell13056]) (by norm_num [cell13056])
      exact ⟨E.1,E.2.trans (by norm_num [cell13056])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy24 (n := 13056) (by norm_num)
        (q := 1 - (cell13056 ⟨24,by decide⟩).lower)
        (by norm_num [cell13056]) (by norm_num [cell13056])
      exact ⟨E.1,E.2.trans (by norm_num [cell13056])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy25 (n := 13056) (by norm_num)
        (q := 1 - (cell13056 ⟨25,by decide⟩).lower)
        (by norm_num [cell13056]) (by norm_num [cell13056])
      exact ⟨E.1,E.2.trans (by norm_num [cell13056])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy26 (n := 13056) (by norm_num)
        (q := 1 - (cell13056 ⟨26,by decide⟩).lower)
        (by norm_num [cell13056]) (by norm_num [cell13056])
      exact ⟨E.1,E.2.trans (by norm_num [cell13056])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy27 (n := 13056) (by norm_num)
        (q := 1 - (cell13056 ⟨27,by decide⟩).lower)
        (by norm_num [cell13056]) (by norm_num [cell13056])
      exact ⟨E.1,E.2.trans (by norm_num [cell13056])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy28 (n := 13056) (by norm_num)
        (q := 1 - (cell13056 ⟨28,by decide⟩).lower)
        (by norm_num [cell13056]) (by norm_num [cell13056])
      exact ⟨E.1,E.2.trans (by norm_num [cell13056])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy29 (n := 13056) (by norm_num)
        (q := 1 - (cell13056 ⟨29,by decide⟩).lower)
        (by norm_num [cell13056]) (by norm_num [cell13056])
      exact ⟨E.1,E.2.trans (by norm_num [cell13056])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy30 (n := 13056) (by norm_num)
        (q := 1 - (cell13056 ⟨30,by decide⟩).lower)
        (by norm_num [cell13056]) (by norm_num [cell13056])
      exact ⟨E.1,E.2.trans (by norm_num [cell13056])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy31 (n := 13056) (by norm_num)
        (q := 1 - (cell13056 ⟨31,by decide⟩).lower)
        (by norm_num [cell13056]) (by norm_num [cell13056])
      exact ⟨E.1,E.2.trans (by norm_num [cell13056])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy32 (n := 13056) (by norm_num)
        (q := 1 - (cell13056 ⟨32,by decide⟩).lower)
        (by norm_num [cell13056]) (by norm_num [cell13056])
      exact ⟨E.1,E.2.trans (by norm_num [cell13056])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy33 (n := 13056) (by norm_num)
        (q := 1 - (cell13056 ⟨33,by decide⟩).lower)
        (by norm_num [cell13056]) (by norm_num [cell13056])
      exact ⟨E.1,E.2.trans (by norm_num [cell13056])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy34 (n := 13056) (by norm_num)
        (q := 1 - (cell13056 ⟨34,by decide⟩).lower)
        (by norm_num [cell13056]) (by norm_num [cell13056])
      exact ⟨E.1,E.2.trans (by norm_num [cell13056])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy35 (n := 13056) (by norm_num)
        (q := 1 - (cell13056 ⟨35,by decide⟩).lower)
        (by norm_num [cell13056]) (by norm_num [cell13056])
      exact ⟨E.1,E.2.trans (by norm_num [cell13056])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy36 (n := 13056) (by norm_num)
        (q := 1 - (cell13056 ⟨36,by decide⟩).lower)
        (by norm_num [cell13056]) (by norm_num [cell13056])
      exact ⟨E.1,E.2.trans (by norm_num [cell13056])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy37 (n := 13056) (by norm_num)
        (q := 1 - (cell13056 ⟨37,by decide⟩).lower)
        (by norm_num [cell13056]) (by norm_num [cell13056])
      exact ⟨E.1,E.2.trans (by norm_num [cell13056])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy38 (n := 13056) (by norm_num)
        (q := 1 - (cell13056 ⟨38,by decide⟩).lower)
        (by norm_num [cell13056]) (by norm_num [cell13056])
      exact ⟨E.1,E.2.trans (by norm_num [cell13056])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy39 (n := 13056) (by norm_num)
        (q := 1 - (cell13056 ⟨39,by decide⟩).lower)
        (by norm_num [cell13056]) (by norm_num [cell13056])
      exact ⟨E.1,E.2.trans (by norm_num [cell13056])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy40 (n := 13056) (by norm_num)
        (q := 1 - (cell13056 ⟨40,by decide⟩).lower)
        (by norm_num [cell13056]) (by norm_num [cell13056])
      exact ⟨E.1,E.2.trans (by norm_num [cell13056])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy41 (n := 13056) (by norm_num)
        (q := 1 - (cell13056 ⟨41,by decide⟩).lower)
        (by norm_num [cell13056]) (by norm_num [cell13056])
      exact ⟨E.1,E.2.trans (by norm_num [cell13056])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy42 (n := 13056) (by norm_num)
        (q := 1 - (cell13056 ⟨42,by decide⟩).lower)
        (by norm_num [cell13056]) (by norm_num [cell13056])
      exact ⟨E.1,E.2.trans (by norm_num [cell13056])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy43 (n := 13056) (by norm_num)
        (q := 1 - (cell13056 ⟨43,by decide⟩).lower)
        (by norm_num [cell13056]) (by norm_num [cell13056])
      exact ⟨E.1,E.2.trans (by norm_num [cell13056])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy44 (n := 13056) (by norm_num)
        (q := 1 - (cell13056 ⟨44,by decide⟩).lower)
        (by norm_num [cell13056]) (by norm_num [cell13056])
      exact ⟨E.1,E.2.trans (by norm_num [cell13056])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy45 (n := 13056) (by norm_num)
        (q := 1 - (cell13056 ⟨45,by decide⟩).lower)
        (by norm_num [cell13056]) (by norm_num [cell13056])
      exact ⟨E.1,E.2.trans (by norm_num [cell13056])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy46 (n := 13056) (by norm_num)
        (q := 1 - (cell13056 ⟨46,by decide⟩).lower)
        (by norm_num [cell13056]) (by norm_num [cell13056])
      exact ⟨E.1,E.2.trans (by norm_num [cell13056])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy47 (n := 13056) (by norm_num)
        (q := 1 - (cell13056 ⟨47,by decide⟩).lower)
        (by norm_num [cell13056]) (by norm_num [cell13056])
      exact ⟨E.1,E.2.trans (by norm_num [cell13056])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy48 (n := 13056) (by norm_num)
        (q := 1 - (cell13056 ⟨48,by decide⟩).lower)
        (by norm_num [cell13056]) (by norm_num [cell13056])
      exact ⟨E.1,E.2.trans (by norm_num [cell13056])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy49 (n := 13056) (by norm_num)
        (q := 1 - (cell13056 ⟨49,by decide⟩).lower)
        (by norm_num [cell13056]) (by norm_num [cell13056])
      exact ⟨E.1,E.2.trans (by norm_num [cell13056])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy50 (n := 13056) (by norm_num)
        (q := 1 - (cell13056 ⟨50,by decide⟩).lower)
        (by norm_num [cell13056]) (by norm_num [cell13056])
      exact ⟨E.1,E.2.trans (by norm_num [cell13056])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy51 (n := 13056) (by norm_num)
        (q := 1 - (cell13056 ⟨51,by decide⟩).lower)
        (by norm_num [cell13056]) (by norm_num [cell13056])
      exact ⟨E.1,E.2.trans (by norm_num [cell13056])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy52 (n := 13056) (by norm_num)
        (q := 1 - (cell13056 ⟨52,by decide⟩).lower)
        (by norm_num [cell13056]) (by norm_num [cell13056])
      exact ⟨E.1,E.2.trans (by norm_num [cell13056])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13056

/-! Source-cell containment and simple scalar guards at 13056. -/
namespace BstLean.Part269.N13056
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13056)
open BstLean.Part268 (cell13056)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13056 ⟨10,by decide⟩).lower ∧ (cell13056 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13056 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13056 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13056 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13056 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13056 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13056,cell13056,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13056 ⟨11,by decide⟩).lower ∧ (cell13056 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13056 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13056 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13056 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13056 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13056 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13056,cell13056,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13056 ⟨12,by decide⟩).lower ∧ (cell13056 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13056 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13056 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13056 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13056 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13056 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13056,cell13056,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13056 ⟨13,by decide⟩).lower ∧ (cell13056 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13056 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13056 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13056 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13056 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13056 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13056,cell13056,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13056 ⟨14,by decide⟩).lower ∧ (cell13056 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13056 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13056 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13056 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13056 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13056 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13056,cell13056,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13056 ⟨15,by decide⟩).lower ∧ (cell13056 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13056 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13056 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13056 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13056 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13056 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13056,cell13056,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13056 ⟨16,by decide⟩).lower ∧ (cell13056 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13056 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13056 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13056 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13056 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13056 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13056,cell13056,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13056 ⟨17,by decide⟩).lower ∧ (cell13056 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13056 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13056 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13056 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13056 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13056 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13056,cell13056,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13056 ⟨18,by decide⟩).lower ∧ (cell13056 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13056 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13056 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13056 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13056 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13056 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13056,cell13056,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13056 ⟨19,by decide⟩).lower ∧ (cell13056 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13056 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13056 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13056 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13056 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13056 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13056,cell13056,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13056 ⟨20,by decide⟩).lower ∧ (cell13056 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13056 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13056 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13056 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13056 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13056 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13056,cell13056,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13056 ⟨21,by decide⟩).lower ∧ (cell13056 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13056 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13056 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13056 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13056 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13056 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13056,cell13056,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13056 ⟨22,by decide⟩).lower ∧ (cell13056 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13056 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13056 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13056 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13056 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13056 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13056,cell13056,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13056 ⟨23,by decide⟩).lower ∧ (cell13056 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13056 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13056 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13056 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13056 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13056 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13056,cell13056,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13056 ⟨24,by decide⟩).lower ∧ (cell13056 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13056 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13056 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13056 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13056 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13056 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13056,cell13056,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13056 ⟨25,by decide⟩).lower ∧ (cell13056 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13056 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13056 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13056 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13056 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13056 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13056,cell13056,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13056 ⟨26,by decide⟩).lower ∧ (cell13056 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13056 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13056 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13056 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13056 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13056 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13056,cell13056,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13056 ⟨27,by decide⟩).lower ∧ (cell13056 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13056 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13056 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13056 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13056 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13056 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13056,cell13056,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13056 ⟨28,by decide⟩).lower ∧ (cell13056 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13056 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13056 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13056 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13056 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13056 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13056,cell13056,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13056 ⟨29,by decide⟩).lower ∧ (cell13056 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13056 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13056 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13056 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13056 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13056 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13056,cell13056,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13056 ⟨30,by decide⟩).lower ∧ (cell13056 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13056 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13056 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13056 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13056 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13056 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13056,cell13056,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13056 ⟨31,by decide⟩).lower ∧ (cell13056 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13056 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13056 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13056 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13056 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13056 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13056,cell13056,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13056 ⟨32,by decide⟩).lower ∧ (cell13056 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13056 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13056 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13056 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13056 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13056 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13056,cell13056,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13056 ⟨33,by decide⟩).lower ∧ (cell13056 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13056 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13056 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13056 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13056 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13056 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13056,cell13056,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13056 ⟨34,by decide⟩).lower ∧ (cell13056 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13056 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13056 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13056 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13056 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13056 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13056,cell13056,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13056 ⟨35,by decide⟩).lower ∧ (cell13056 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13056 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13056 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13056 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13056 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13056 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13056,cell13056,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13056 ⟨36,by decide⟩).lower ∧ (cell13056 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13056 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13056 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13056 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13056 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13056 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13056,cell13056,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13056 ⟨37,by decide⟩).lower ∧ (cell13056 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13056 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13056 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13056 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13056 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13056 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13056,cell13056,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13056 ⟨38,by decide⟩).lower ∧ (cell13056 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13056 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13056 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13056 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13056 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13056 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13056,cell13056,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13056 ⟨39,by decide⟩).lower ∧ (cell13056 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13056 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13056 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13056 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13056 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13056 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13056,cell13056,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13056 ⟨40,by decide⟩).lower ∧ (cell13056 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13056 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13056 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13056 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13056 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13056 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13056,cell13056,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13056 ⟨41,by decide⟩).lower ∧ (cell13056 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13056 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13056 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13056 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13056 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13056 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13056,cell13056,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13056 ⟨42,by decide⟩).lower ∧ (cell13056 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13056 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13056 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13056 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13056 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13056 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13056,cell13056,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13056 ⟨43,by decide⟩).lower ∧ (cell13056 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13056 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13056 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13056 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13056 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13056 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13056,cell13056,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13056 ⟨44,by decide⟩).lower ∧ (cell13056 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13056 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13056 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13056 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13056 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13056 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13056,cell13056,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13056 ⟨45,by decide⟩).lower ∧ (cell13056 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13056 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13056 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13056 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13056 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13056 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13056,cell13056,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13056 ⟨46,by decide⟩).lower ∧ (cell13056 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13056 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13056 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13056 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13056 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13056 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13056,cell13056,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13056 ⟨47,by decide⟩).lower ∧ (cell13056 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13056 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13056 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13056 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13056 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13056 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13056,cell13056,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13056 ⟨48,by decide⟩).lower ∧ (cell13056 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13056 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13056 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13056 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13056 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13056 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13056,cell13056,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13056 ⟨49,by decide⟩).lower ∧ (cell13056 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13056 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13056 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13056 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13056 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13056 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13056,cell13056,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13056 ⟨50,by decide⟩).lower ∧ (cell13056 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13056 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13056 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13056 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13056 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13056 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13056,cell13056,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13056 ⟨51,by decide⟩).lower ∧ (cell13056 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13056 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13056 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13056 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13056 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13056 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13056,cell13056,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13056 ⟨52,by decide⟩).lower ∧ (cell13056 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13056 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13056 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13056 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13056 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13056 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13056,cell13056,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13056 i).lower ∧
    (cell13056 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13056 i).upper ≤ (0.532 : ℝ) ∧
    (cell13056 i).centre ≤ (0.1 : ℝ) ∧ (cell13056 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13056 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13056 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13056

/-! The local source numeric instances at 13056 have no network premises. -/
namespace BstLean.Part269.N13056
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13056)
open BstLean.Part268 (cell13056)

noncomputable def sourceNumerics13056 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13056 (cell13056 i)
      scalarRow13056.M scalarRow13056.H scalarRow13056.xi := by
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
    energy_allowance := scalarRow13056.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13056]
    centre_nonneg := (scalarRow13056.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D28.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13056])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13056
/-! Actual 13057 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13057
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13057 ≤ (1.035312010615 : ℝ) := by
  have hr : (114.267230648160 : ℝ) ≤ √(13057 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.267230648160 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13057 13057 (11 / 1000) ≤
    (0.008365363571 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13057) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.267230648160 : ℝ) ≤ √(13057 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13057)
  have hdiv : K / √(13057 : ℝ) ≤ K / 114.267230648160 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.267230648160 ≤ (0.008365363571 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13057.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13057 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13057 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13057 := gPlus_lower 13057
end BstLean.Part269.N13057

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13057
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035312010614 : ℝ) ≤ wn 13057 := by
  have hn : √(13057 : ℝ) ≤ 114.267230648161 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13057 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.267230648161 ≤ 2 / √(13057 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000244876427 : ℝ) ≤ rhoBar 13057 BstLean.Part154.csC ∧
    rhoBar 13057 BstLean.Part154.csC ≤ 0.000244876806 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035312010614 : ℝ) / (1.295212 * 13057) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035312010615 : ℝ) / (1.29521 * 13057) := by gcongr
      _ ≤ (0.000244876806 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13057 BstLean.Part154.csC) ≤ 0.000979567189 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13057 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13057 BstLean.Part154.csC) (piBar (rhoBar 13057 BstLean.Part154.csC)) ≤ 0.000187038314 ∧
    cc1 (rhoBar 13057 BstLean.Part154.csC) (piBar (rhoBar 13057 BstLean.Part154.csC)) ≤ 0.000119013771 ∧
    cc2 (rhoBar 13057 BstLean.Part154.csC) ≤ 0.000069088466 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13057 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13057 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13057 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13057 BstLean.Part154.csC * nuR (rhoBar 13057 BstLean.Part154.csC)) ≤ 0.000489768604 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000244876806 : ℝ) * 0.000979567189 := by gcongr
      _ ≤ (0.000489768604 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13057 BstLean.Part154.csC) * nuR (rhoBar 13057 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000979567189 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13057 BstLean.Part154.csC) * rhoBar 13057 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000244876806 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000244876806 / 2 + 0.399 * 0.000979567189 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000187038314 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000489768604 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119013771 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000244876806 / 1.414213562 := by gcongr
      _ ≤ (0.000069088466 : ℝ) := by norm_num

end BstLean.Part269.N13057

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13057
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13057 BstLean.Part154.csC) (piBar (rhoBar 13057 BstLean.Part154.csC)) ≤ 1.51077E-7 := by
  have hr0 : 0 ≤ rhoBar 13057 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13057 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13057 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13057 BstLean.Part154.csC) (piBar (rhoBar 13057 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13057 BstLean.Part154.csC) (piBar (rhoBar 13057 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13057 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000187038314 : ℝ) ^ 2 + 0.000119013771 ^ 2 + 3 * 0.000069088466 ^ 2 +
        2 * 0.797885 * 0.000187038314 * 0.000119013771 + 2 * 0.000187038314 * 0.000069088466 +
        4 * 0.797885 * 0.000119013771 * 0.000069088466 := by gcongr
    _ ≤ (1.51077E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13057 BstLean.Part154.csC Θ ≤ 0.002554951239 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13057 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13057 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13057 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13057 BstLean.Part154.csC) (piBar (rhoBar 13057 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13057 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035312010615 * 1.51077E-7 / (0.000244876427 : ℝ) := by gcongr
    _ ≤ 0.002554951239 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13057 BstLean.Part154.csC Θ ≤ 0.002833483880 + 0.000645593441 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13057 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13057 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13057 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035312010615 : ℝ) * ((2 * Θ * 0.000244876806 +
        (6863 / 10000) * 0.000244876806 * 13057 * 0.000979567189) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002833483880 + 0.000645593441 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13057 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13057 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13057 0.011 Θ ∧ gammaRatio 13057 0.011 Θ ≤ 0.000084182314 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13057 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035312010615 : ℝ) * 0.525 / ((1 - 0.011) * 13057) := by gcongr
      _ ≤ (0.000084182314 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13057 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13057 0.011 Θ) :=
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
    badAllowance 13057 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000383749387 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13057 BstLean.Part154.csC) 1.22 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 2 (rhoBar 13057 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13057 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13057 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13057 0.011 Θ) 1.12 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 1 (gammaRatio 13057 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13057 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13057 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13057 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13057 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035312010615 : ℝ) * 13057 *
        (1.3781E-8 / 1.1045361 + 1.6832E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000383749387 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13057 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003217233267 + 0.003200544680 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13057

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13057
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13057 BstLean.Part154.csC) (piBar (rhoBar 13057 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13057 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13057 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13057 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13057 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13057 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13057 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13057 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13057 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13057 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13057 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13057 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13057 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13057 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13057 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051754109829 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13057) ≤ 0.010451269138 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13057 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035312010615)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010451269138 + 2 * 0.737676 / 13057) := by gcongr
    _ ≤ (0.051754109829 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13057 12 ≤ 0.0015 := by
  exact BstLean.Part269.S28.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13057

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13057
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560519271471 : ℝ) ≤ plow 13057 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13057) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052404119224)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001341349401) : eMP 13057 0.011 xi bn ≤ 0.001155248617 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13057 : ℝ) * (1 - 0.011))) ≤ 0.000571249815 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001341349401 / (13057 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000571249815 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000571249815 : ℝ) + 3.141593 * 0.052404119224 / (13057 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001155248617 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052404119224)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001341349401) : PiBarMP 13057 12 0.011 xi bn ≤ 0.159009560386 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13057 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036624437211 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.637023016268 : ℝ) ≤ √((13057 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.267230648160 : ℝ) ≤ √(13057 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13057) ≤ 0.121928291985 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036624437211 + 0.052404119224 * 1.772454 / (2 * (113.637023016268 : ℝ))) * (1 + 0.001155248617) +
        8 / (13057 * 114.267230648160) + 0.121928291985 := by gcongr
    _ ≤ (0.159009560386 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052404119224)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001341349401) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280673569955) :
    parallelOracle 13057 0.011 xi bn cd ≤ 0.159972943601 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13057 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13057 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560519271471 : ℝ) ≤ plow 13057 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.267230648160 : ℝ) ≤ √(13057 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280673569955 : ℝ) / (2 * 0.560519271471 * 114.267230648160)) * 0.159009560386 +
        0.280673569955 ^ 2 / (2 * 0.560519271471 * 114.267230648160) := by gcongr
    _ ≤ (0.159972943601 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052404119224) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001341349401)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280673569955) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13057 13057 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560519271471 : ℝ) ≤ plow 13057 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.267230648160 : ℝ) ≤ √(13057 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13057 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13057 Θ 1.22 ≤ 0.011605256315 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.267230648160 := by gcongr <;> linarith
      _ ≤ (0.011605256315 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13057 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13057 13057 0.011 ≤ 0.008365363571 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13057 13057 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13057 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13057 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13057 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13057 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159972943601 + 0.011605256315 + (0.008365363571 : ℝ) *
        (1 + 2 * (0.280673569955 + 0.011605256315) / (0.560519271471 * 114.267230648160))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13057]

end BstLean.Part269.N13057

/-! The original eight local profiles supply actual 13057 moment certificates. -/
namespace BstLean.Part269.N13057
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13057 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13057 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13057 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052404119224 ∧
    0 ≤ bN 13057 BstLean.Part154.csC (groupTheta g) ∧ bN 13057 BstLean.Part154.csC (groupTheta g) ≤ 0.001341349401 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13057 13057 0.011
      (momentAllowance 13057 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13057 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13057 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13057 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13057 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13057 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228919460126 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13057 0.011
      (momentAllowance 13057 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13057 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13057
/-! The actual computed-centre upper energy formula at 13057. -/
namespace BstLean.Part269.N13057
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13057

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13057
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13057)
open BstLean.Part268 (cell13057)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084512143068
  | 2 => 0.085438891611
  | 3 => 0.086361560287
  | 4 => 0.087281045531
  | 5 => 0.088198446767
  | 6 => 0.089115098415
  | 7 => 0.090032605279
  | 8 => 0.090952881397
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13057 13057 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13057 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003218831707 + 0.003202305177 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S28.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13057

/-! Actual upper energy certificates on all 43 source endpoints at 13057. -/
namespace BstLean.Part269.N13057
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13057)
open BstLean.Part268 (cell13057)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13057 (gMinus 13057) (1 - (cell13057 i).lower) ≤ 1 ∧
    energyUpper 13057 (gMinus 13057) (BstLean.Part211.gPlus 13057)
      (finiteEnergy 13057 13057 0.011) (1 - (cell13057 i).lower) ≤
      (cell13057 i).energy := by
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
      have E := BstLean.Part269.S28.uniformEnergy10 (n := 13057) (by norm_num)
        (q := 1 - (cell13057 ⟨10,by decide⟩).lower)
        (by norm_num [cell13057]) (by norm_num [cell13057])
      exact ⟨E.1,E.2.trans (by norm_num [cell13057])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy11 (n := 13057) (by norm_num)
        (q := 1 - (cell13057 ⟨11,by decide⟩).lower)
        (by norm_num [cell13057]) (by norm_num [cell13057])
      exact ⟨E.1,E.2.trans (by norm_num [cell13057])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy12 (n := 13057) (by norm_num)
        (q := 1 - (cell13057 ⟨12,by decide⟩).lower)
        (by norm_num [cell13057]) (by norm_num [cell13057])
      exact ⟨E.1,E.2.trans (by norm_num [cell13057])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy13 (n := 13057) (by norm_num)
        (q := 1 - (cell13057 ⟨13,by decide⟩).lower)
        (by norm_num [cell13057]) (by norm_num [cell13057])
      exact ⟨E.1,E.2.trans (by norm_num [cell13057])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy14 (n := 13057) (by norm_num)
        (q := 1 - (cell13057 ⟨14,by decide⟩).lower)
        (by norm_num [cell13057]) (by norm_num [cell13057])
      exact ⟨E.1,E.2.trans (by norm_num [cell13057])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy15 (n := 13057) (by norm_num)
        (q := 1 - (cell13057 ⟨15,by decide⟩).lower)
        (by norm_num [cell13057]) (by norm_num [cell13057])
      exact ⟨E.1,E.2.trans (by norm_num [cell13057])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy16 (n := 13057) (by norm_num)
        (q := 1 - (cell13057 ⟨16,by decide⟩).lower)
        (by norm_num [cell13057]) (by norm_num [cell13057])
      exact ⟨E.1,E.2.trans (by norm_num [cell13057])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy17 (n := 13057) (by norm_num)
        (q := 1 - (cell13057 ⟨17,by decide⟩).lower)
        (by norm_num [cell13057]) (by norm_num [cell13057])
      exact ⟨E.1,E.2.trans (by norm_num [cell13057])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy18 (n := 13057) (by norm_num)
        (q := 1 - (cell13057 ⟨18,by decide⟩).lower)
        (by norm_num [cell13057]) (by norm_num [cell13057])
      exact ⟨E.1,E.2.trans (by norm_num [cell13057])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy19 (n := 13057) (by norm_num)
        (q := 1 - (cell13057 ⟨19,by decide⟩).lower)
        (by norm_num [cell13057]) (by norm_num [cell13057])
      exact ⟨E.1,E.2.trans (by norm_num [cell13057])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy20 (n := 13057) (by norm_num)
        (q := 1 - (cell13057 ⟨20,by decide⟩).lower)
        (by norm_num [cell13057]) (by norm_num [cell13057])
      exact ⟨E.1,E.2.trans (by norm_num [cell13057])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy21 (n := 13057) (by norm_num)
        (q := 1 - (cell13057 ⟨21,by decide⟩).lower)
        (by norm_num [cell13057]) (by norm_num [cell13057])
      exact ⟨E.1,E.2.trans (by norm_num [cell13057])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy22 (n := 13057) (by norm_num)
        (q := 1 - (cell13057 ⟨22,by decide⟩).lower)
        (by norm_num [cell13057]) (by norm_num [cell13057])
      exact ⟨E.1,E.2.trans (by norm_num [cell13057])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy23 (n := 13057) (by norm_num)
        (q := 1 - (cell13057 ⟨23,by decide⟩).lower)
        (by norm_num [cell13057]) (by norm_num [cell13057])
      exact ⟨E.1,E.2.trans (by norm_num [cell13057])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy24 (n := 13057) (by norm_num)
        (q := 1 - (cell13057 ⟨24,by decide⟩).lower)
        (by norm_num [cell13057]) (by norm_num [cell13057])
      exact ⟨E.1,E.2.trans (by norm_num [cell13057])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy25 (n := 13057) (by norm_num)
        (q := 1 - (cell13057 ⟨25,by decide⟩).lower)
        (by norm_num [cell13057]) (by norm_num [cell13057])
      exact ⟨E.1,E.2.trans (by norm_num [cell13057])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy26 (n := 13057) (by norm_num)
        (q := 1 - (cell13057 ⟨26,by decide⟩).lower)
        (by norm_num [cell13057]) (by norm_num [cell13057])
      exact ⟨E.1,E.2.trans (by norm_num [cell13057])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy27 (n := 13057) (by norm_num)
        (q := 1 - (cell13057 ⟨27,by decide⟩).lower)
        (by norm_num [cell13057]) (by norm_num [cell13057])
      exact ⟨E.1,E.2.trans (by norm_num [cell13057])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy28 (n := 13057) (by norm_num)
        (q := 1 - (cell13057 ⟨28,by decide⟩).lower)
        (by norm_num [cell13057]) (by norm_num [cell13057])
      exact ⟨E.1,E.2.trans (by norm_num [cell13057])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy29 (n := 13057) (by norm_num)
        (q := 1 - (cell13057 ⟨29,by decide⟩).lower)
        (by norm_num [cell13057]) (by norm_num [cell13057])
      exact ⟨E.1,E.2.trans (by norm_num [cell13057])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy30 (n := 13057) (by norm_num)
        (q := 1 - (cell13057 ⟨30,by decide⟩).lower)
        (by norm_num [cell13057]) (by norm_num [cell13057])
      exact ⟨E.1,E.2.trans (by norm_num [cell13057])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy31 (n := 13057) (by norm_num)
        (q := 1 - (cell13057 ⟨31,by decide⟩).lower)
        (by norm_num [cell13057]) (by norm_num [cell13057])
      exact ⟨E.1,E.2.trans (by norm_num [cell13057])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy32 (n := 13057) (by norm_num)
        (q := 1 - (cell13057 ⟨32,by decide⟩).lower)
        (by norm_num [cell13057]) (by norm_num [cell13057])
      exact ⟨E.1,E.2.trans (by norm_num [cell13057])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy33 (n := 13057) (by norm_num)
        (q := 1 - (cell13057 ⟨33,by decide⟩).lower)
        (by norm_num [cell13057]) (by norm_num [cell13057])
      exact ⟨E.1,E.2.trans (by norm_num [cell13057])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy34 (n := 13057) (by norm_num)
        (q := 1 - (cell13057 ⟨34,by decide⟩).lower)
        (by norm_num [cell13057]) (by norm_num [cell13057])
      exact ⟨E.1,E.2.trans (by norm_num [cell13057])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy35 (n := 13057) (by norm_num)
        (q := 1 - (cell13057 ⟨35,by decide⟩).lower)
        (by norm_num [cell13057]) (by norm_num [cell13057])
      exact ⟨E.1,E.2.trans (by norm_num [cell13057])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy36 (n := 13057) (by norm_num)
        (q := 1 - (cell13057 ⟨36,by decide⟩).lower)
        (by norm_num [cell13057]) (by norm_num [cell13057])
      exact ⟨E.1,E.2.trans (by norm_num [cell13057])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy37 (n := 13057) (by norm_num)
        (q := 1 - (cell13057 ⟨37,by decide⟩).lower)
        (by norm_num [cell13057]) (by norm_num [cell13057])
      exact ⟨E.1,E.2.trans (by norm_num [cell13057])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy38 (n := 13057) (by norm_num)
        (q := 1 - (cell13057 ⟨38,by decide⟩).lower)
        (by norm_num [cell13057]) (by norm_num [cell13057])
      exact ⟨E.1,E.2.trans (by norm_num [cell13057])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy39 (n := 13057) (by norm_num)
        (q := 1 - (cell13057 ⟨39,by decide⟩).lower)
        (by norm_num [cell13057]) (by norm_num [cell13057])
      exact ⟨E.1,E.2.trans (by norm_num [cell13057])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy40 (n := 13057) (by norm_num)
        (q := 1 - (cell13057 ⟨40,by decide⟩).lower)
        (by norm_num [cell13057]) (by norm_num [cell13057])
      exact ⟨E.1,E.2.trans (by norm_num [cell13057])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy41 (n := 13057) (by norm_num)
        (q := 1 - (cell13057 ⟨41,by decide⟩).lower)
        (by norm_num [cell13057]) (by norm_num [cell13057])
      exact ⟨E.1,E.2.trans (by norm_num [cell13057])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy42 (n := 13057) (by norm_num)
        (q := 1 - (cell13057 ⟨42,by decide⟩).lower)
        (by norm_num [cell13057]) (by norm_num [cell13057])
      exact ⟨E.1,E.2.trans (by norm_num [cell13057])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy43 (n := 13057) (by norm_num)
        (q := 1 - (cell13057 ⟨43,by decide⟩).lower)
        (by norm_num [cell13057]) (by norm_num [cell13057])
      exact ⟨E.1,E.2.trans (by norm_num [cell13057])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy44 (n := 13057) (by norm_num)
        (q := 1 - (cell13057 ⟨44,by decide⟩).lower)
        (by norm_num [cell13057]) (by norm_num [cell13057])
      exact ⟨E.1,E.2.trans (by norm_num [cell13057])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy45 (n := 13057) (by norm_num)
        (q := 1 - (cell13057 ⟨45,by decide⟩).lower)
        (by norm_num [cell13057]) (by norm_num [cell13057])
      exact ⟨E.1,E.2.trans (by norm_num [cell13057])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy46 (n := 13057) (by norm_num)
        (q := 1 - (cell13057 ⟨46,by decide⟩).lower)
        (by norm_num [cell13057]) (by norm_num [cell13057])
      exact ⟨E.1,E.2.trans (by norm_num [cell13057])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy47 (n := 13057) (by norm_num)
        (q := 1 - (cell13057 ⟨47,by decide⟩).lower)
        (by norm_num [cell13057]) (by norm_num [cell13057])
      exact ⟨E.1,E.2.trans (by norm_num [cell13057])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy48 (n := 13057) (by norm_num)
        (q := 1 - (cell13057 ⟨48,by decide⟩).lower)
        (by norm_num [cell13057]) (by norm_num [cell13057])
      exact ⟨E.1,E.2.trans (by norm_num [cell13057])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy49 (n := 13057) (by norm_num)
        (q := 1 - (cell13057 ⟨49,by decide⟩).lower)
        (by norm_num [cell13057]) (by norm_num [cell13057])
      exact ⟨E.1,E.2.trans (by norm_num [cell13057])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy50 (n := 13057) (by norm_num)
        (q := 1 - (cell13057 ⟨50,by decide⟩).lower)
        (by norm_num [cell13057]) (by norm_num [cell13057])
      exact ⟨E.1,E.2.trans (by norm_num [cell13057])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy51 (n := 13057) (by norm_num)
        (q := 1 - (cell13057 ⟨51,by decide⟩).lower)
        (by norm_num [cell13057]) (by norm_num [cell13057])
      exact ⟨E.1,E.2.trans (by norm_num [cell13057])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy52 (n := 13057) (by norm_num)
        (q := 1 - (cell13057 ⟨52,by decide⟩).lower)
        (by norm_num [cell13057]) (by norm_num [cell13057])
      exact ⟨E.1,E.2.trans (by norm_num [cell13057])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13057

/-! Source-cell containment and simple scalar guards at 13057. -/
namespace BstLean.Part269.N13057
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13057)
open BstLean.Part268 (cell13057)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13057 ⟨10,by decide⟩).lower ∧ (cell13057 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13057 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13057 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13057 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13057 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13057 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13057,cell13057,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13057 ⟨11,by decide⟩).lower ∧ (cell13057 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13057 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13057 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13057 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13057 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13057 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13057,cell13057,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13057 ⟨12,by decide⟩).lower ∧ (cell13057 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13057 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13057 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13057 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13057 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13057 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13057,cell13057,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13057 ⟨13,by decide⟩).lower ∧ (cell13057 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13057 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13057 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13057 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13057 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13057 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13057,cell13057,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13057 ⟨14,by decide⟩).lower ∧ (cell13057 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13057 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13057 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13057 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13057 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13057 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13057,cell13057,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13057 ⟨15,by decide⟩).lower ∧ (cell13057 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13057 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13057 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13057 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13057 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13057 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13057,cell13057,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13057 ⟨16,by decide⟩).lower ∧ (cell13057 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13057 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13057 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13057 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13057 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13057 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13057,cell13057,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13057 ⟨17,by decide⟩).lower ∧ (cell13057 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13057 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13057 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13057 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13057 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13057 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13057,cell13057,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13057 ⟨18,by decide⟩).lower ∧ (cell13057 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13057 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13057 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13057 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13057 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13057 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13057,cell13057,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13057 ⟨19,by decide⟩).lower ∧ (cell13057 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13057 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13057 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13057 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13057 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13057 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13057,cell13057,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13057 ⟨20,by decide⟩).lower ∧ (cell13057 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13057 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13057 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13057 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13057 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13057 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13057,cell13057,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13057 ⟨21,by decide⟩).lower ∧ (cell13057 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13057 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13057 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13057 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13057 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13057 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13057,cell13057,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13057 ⟨22,by decide⟩).lower ∧ (cell13057 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13057 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13057 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13057 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13057 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13057 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13057,cell13057,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13057 ⟨23,by decide⟩).lower ∧ (cell13057 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13057 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13057 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13057 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13057 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13057 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13057,cell13057,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13057 ⟨24,by decide⟩).lower ∧ (cell13057 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13057 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13057 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13057 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13057 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13057 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13057,cell13057,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13057 ⟨25,by decide⟩).lower ∧ (cell13057 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13057 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13057 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13057 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13057 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13057 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13057,cell13057,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13057 ⟨26,by decide⟩).lower ∧ (cell13057 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13057 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13057 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13057 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13057 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13057 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13057,cell13057,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13057 ⟨27,by decide⟩).lower ∧ (cell13057 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13057 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13057 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13057 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13057 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13057 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13057,cell13057,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13057 ⟨28,by decide⟩).lower ∧ (cell13057 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13057 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13057 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13057 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13057 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13057 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13057,cell13057,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13057 ⟨29,by decide⟩).lower ∧ (cell13057 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13057 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13057 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13057 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13057 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13057 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13057,cell13057,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13057 ⟨30,by decide⟩).lower ∧ (cell13057 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13057 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13057 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13057 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13057 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13057 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13057,cell13057,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13057 ⟨31,by decide⟩).lower ∧ (cell13057 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13057 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13057 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13057 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13057 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13057 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13057,cell13057,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13057 ⟨32,by decide⟩).lower ∧ (cell13057 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13057 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13057 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13057 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13057 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13057 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13057,cell13057,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13057 ⟨33,by decide⟩).lower ∧ (cell13057 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13057 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13057 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13057 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13057 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13057 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13057,cell13057,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13057 ⟨34,by decide⟩).lower ∧ (cell13057 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13057 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13057 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13057 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13057 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13057 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13057,cell13057,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13057 ⟨35,by decide⟩).lower ∧ (cell13057 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13057 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13057 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13057 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13057 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13057 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13057,cell13057,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13057 ⟨36,by decide⟩).lower ∧ (cell13057 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13057 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13057 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13057 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13057 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13057 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13057,cell13057,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13057 ⟨37,by decide⟩).lower ∧ (cell13057 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13057 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13057 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13057 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13057 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13057 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13057,cell13057,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13057 ⟨38,by decide⟩).lower ∧ (cell13057 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13057 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13057 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13057 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13057 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13057 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13057,cell13057,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13057 ⟨39,by decide⟩).lower ∧ (cell13057 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13057 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13057 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13057 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13057 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13057 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13057,cell13057,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13057 ⟨40,by decide⟩).lower ∧ (cell13057 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13057 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13057 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13057 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13057 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13057 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13057,cell13057,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13057 ⟨41,by decide⟩).lower ∧ (cell13057 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13057 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13057 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13057 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13057 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13057 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13057,cell13057,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13057 ⟨42,by decide⟩).lower ∧ (cell13057 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13057 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13057 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13057 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13057 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13057 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13057,cell13057,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13057 ⟨43,by decide⟩).lower ∧ (cell13057 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13057 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13057 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13057 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13057 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13057 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13057,cell13057,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13057 ⟨44,by decide⟩).lower ∧ (cell13057 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13057 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13057 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13057 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13057 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13057 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13057,cell13057,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13057 ⟨45,by decide⟩).lower ∧ (cell13057 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13057 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13057 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13057 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13057 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13057 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13057,cell13057,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13057 ⟨46,by decide⟩).lower ∧ (cell13057 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13057 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13057 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13057 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13057 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13057 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13057,cell13057,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13057 ⟨47,by decide⟩).lower ∧ (cell13057 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13057 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13057 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13057 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13057 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13057 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13057,cell13057,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13057 ⟨48,by decide⟩).lower ∧ (cell13057 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13057 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13057 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13057 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13057 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13057 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13057,cell13057,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13057 ⟨49,by decide⟩).lower ∧ (cell13057 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13057 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13057 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13057 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13057 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13057 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13057,cell13057,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13057 ⟨50,by decide⟩).lower ∧ (cell13057 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13057 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13057 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13057 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13057 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13057 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13057,cell13057,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13057 ⟨51,by decide⟩).lower ∧ (cell13057 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13057 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13057 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13057 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13057 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13057 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13057,cell13057,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13057 ⟨52,by decide⟩).lower ∧ (cell13057 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13057 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13057 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13057 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13057 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13057 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13057,cell13057,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13057 i).lower ∧
    (cell13057 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13057 i).upper ≤ (0.532 : ℝ) ∧
    (cell13057 i).centre ≤ (0.1 : ℝ) ∧ (cell13057 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13057 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13057 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13057

/-! The local source numeric instances at 13057 have no network premises. -/
namespace BstLean.Part269.N13057
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13057)
open BstLean.Part268 (cell13057)

noncomputable def sourceNumerics13057 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13057 (cell13057 i)
      scalarRow13057.M scalarRow13057.H scalarRow13057.xi := by
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
    energy_allowance := scalarRow13057.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13057]
    centre_nonneg := (scalarRow13057.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D28.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13057])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13057
/-! Actual 13058 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13058
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13058 ≤ (1.035310646737 : ℝ) := by
  have hr : (114.271606272074 : ℝ) ≤ √(13058 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.271606272074 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13058 13058 (11 / 1000) ≤
    (0.008365043247 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13058) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.271606272074 : ℝ) ≤ √(13058 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13058)
  have hdiv : K / √(13058 : ℝ) ≤ K / 114.271606272074 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.271606272074 ≤ (0.008365043247 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13058.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13058 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13058 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13058 := gPlus_lower 13058
end BstLean.Part269.N13058

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13058
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035310646736 : ℝ) ≤ wn 13058 := by
  have hn : √(13058 : ℝ) ≤ 114.271606272075 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13058 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.271606272075 ≤ 2 / √(13058 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000244857351 : ℝ) ≤ rhoBar 13058 BstLean.Part154.csC ∧
    rhoBar 13058 BstLean.Part154.csC ≤ 0.000244857730 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035310646736 : ℝ) / (1.295212 * 13058) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035310646737 : ℝ) / (1.29521 * 13058) := by gcongr
      _ ≤ (0.000244857730 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13058 BstLean.Part154.csC) ≤ 0.000979490876 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13058 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13058 BstLean.Part154.csC) (piBar (rhoBar 13058 BstLean.Part154.csC)) ≤ 0.000187023743 ∧
    cc1 (rhoBar 13058 BstLean.Part154.csC) (piBar (rhoBar 13058 BstLean.Part154.csC)) ≤ 0.000119004500 ∧
    cc2 (rhoBar 13058 BstLean.Part154.csC) ≤ 0.000069083084 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13058 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13058 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13058 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13058 BstLean.Part154.csC * nuR (rhoBar 13058 BstLean.Part154.csC)) ≤ 0.000489730449 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000244857730 : ℝ) * 0.000979490876 := by gcongr
      _ ≤ (0.000489730449 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13058 BstLean.Part154.csC) * nuR (rhoBar 13058 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000979490876 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13058 BstLean.Part154.csC) * rhoBar 13058 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000244857730 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000244857730 / 2 + 0.399 * 0.000979490876 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000187023743 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000489730449 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119004500 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000244857730 / 1.414213562 := by gcongr
      _ ≤ (0.000069083084 : ℝ) := by norm_num

end BstLean.Part269.N13058

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13058
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13058 BstLean.Part154.csC) (piBar (rhoBar 13058 BstLean.Part154.csC)) ≤ 1.51053E-7 := by
  have hr0 : 0 ≤ rhoBar 13058 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13058 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13058 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13058 BstLean.Part154.csC) (piBar (rhoBar 13058 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13058 BstLean.Part154.csC) (piBar (rhoBar 13058 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13058 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000187023743 : ℝ) ^ 2 + 0.000119004500 ^ 2 + 3 * 0.000069083084 ^ 2 +
        2 * 0.797885 * 0.000187023743 * 0.000119004500 + 2 * 0.000187023743 * 0.000069083084 +
        4 * 0.797885 * 0.000119004500 * 0.000069083084 := by gcongr
    _ ≤ (1.51053E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13058 BstLean.Part154.csC Θ ≤ 0.002554741012 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13058 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13058 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13058 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13058 BstLean.Part154.csC) (piBar (rhoBar 13058 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13058 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035310646737 * 1.51053E-7 / (0.000244857351 : ℝ) := by gcongr
    _ ≤ 0.002554741012 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13058 BstLean.Part154.csC Θ ≤ 0.002833255668 + 0.000645542298 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13058 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13058 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13058 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035310646737 : ℝ) * ((2 * Θ * 0.000244857730 +
        (6863 / 10000) * 0.000244857730 * 13058 * 0.000979490876) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002833255668 + 0.000645542298 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13058 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13058 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13058 0.011 Θ ∧ gammaRatio 13058 0.011 Θ ≤ 0.000084175756 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13058 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035310646737 : ℝ) * 0.525 / ((1 - 0.011) * 13058) := by gcongr
      _ ≤ (0.000084175756 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13058 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13058 0.011 Θ) :=
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
    badAllowance 13058 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000383749387 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13058 BstLean.Part154.csC) 1.22 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 2 (rhoBar 13058 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13058 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13058 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13058 0.011 Θ) 1.12 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 1 (gammaRatio 13058 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13058 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13058 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13058 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13058 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035310646737 : ℝ) * 13058 *
        (1.3781E-8 / 1.1045361 + 1.6832E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000383749387 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13058 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003217005055 + 0.003200283310 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13058

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13058
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13058 BstLean.Part154.csC) (piBar (rhoBar 13058 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13058 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13058 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13058 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13058 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13058 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13058 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13058 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13058 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13058 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13058 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13058 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13058 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13058 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13058 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051752106890 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13058) ≤ 0.010450868943 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13058 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035310646737)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010450868943 + 2 * 0.737676 / 13058) := by gcongr
    _ ≤ (0.051752106890 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13058 12 ≤ 0.0015 := by
  exact BstLean.Part269.S28.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13058

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13058
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560519314251 : ℝ) ≤ plow 13058 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13058) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052403753793)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001341239032) : eMP 13058 0.011 xi bn ≤ 0.001155156801 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13058 : ℝ) * (1 - 0.011))) ≤ 0.000571204440 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001341239032 / (13058 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000571204440 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000571204440 : ℝ) + 3.141593 * 0.052403753793 / (13058 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001155156801 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052403753793)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001341239032) : PiBarMP 13058 12 0.011 xi bn ≤ 0.159003360502 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13058 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036622930413 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.641374507702 : ℝ) ≤ √((13058 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.271606272074 : ℝ) ≤ √(13058 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13058) ≤ 0.121923623176 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036622930413 + 0.052403753793 * 1.772454 / (2 * (113.641374507702 : ℝ))) * (1 + 0.001155156801) +
        8 / (13058 * 114.271606272074) + 0.121923623176 := by gcongr
    _ ≤ (0.159003360502 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052403753793)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001341239032) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280670768849) :
    parallelOracle 13058 0.011 xi bn cd ≤ 0.159966677419 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13058 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13058 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560519314251 : ℝ) ≤ plow 13058 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.271606272074 : ℝ) ≤ √(13058 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280670768849 : ℝ) / (2 * 0.560519314251 * 114.271606272074)) * 0.159003360502 +
        0.280670768849 ^ 2 / (2 * 0.560519314251 * 114.271606272074) := by gcongr
    _ ≤ (0.159966677419 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052403753793) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001341239032)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280670768849) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13058 13058 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560519314251 : ℝ) ≤ plow 13058 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.271606272074 : ℝ) ≤ √(13058 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13058 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13058 Θ 1.22 ≤ 0.011604811933 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.271606272074 := by gcongr <;> linarith
      _ ≤ (0.011604811933 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13058 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13058 13058 0.011 ≤ 0.008365043247 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13058 13058 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13058 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13058 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13058 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13058 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159966677419 + 0.011604811933 + (0.008365043247 : ℝ) *
        (1 + 2 * (0.280670768849 + 0.011604811933) / (0.560519314251 * 114.271606272074))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13058]

end BstLean.Part269.N13058

/-! The original eight local profiles supply actual 13058 moment certificates. -/
namespace BstLean.Part269.N13058
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13058 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13058 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13058 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052403753793 ∧
    0 ≤ bN 13058 BstLean.Part154.csC (groupTheta g) ∧ bN 13058 BstLean.Part154.csC (groupTheta g) ≤ 0.001341239032 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13058 13058 0.011
      (momentAllowance 13058 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13058 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13058 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13058 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13058 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13058 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228918661959 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13058 0.011
      (momentAllowance 13058 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13058 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13058
/-! The actual computed-centre upper energy formula at 13058. -/
namespace BstLean.Part269.N13058
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13058

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13058
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13058)
open BstLean.Part268 (cell13058)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084509569684
  | 2 => 0.085436285247
  | 3 => 0.086358916064
  | 4 => 0.087278357419
  | 5 => 0.088195707371
  | 6 => 0.089112298739
  | 7 => 0.090029734450
  | 8 => 0.090949926367
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13058 13058 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13058 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003218831707 + 0.003202305177 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S28.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13058

/-! Actual upper energy certificates on all 43 source endpoints at 13058. -/
namespace BstLean.Part269.N13058
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13058)
open BstLean.Part268 (cell13058)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13058 (gMinus 13058) (1 - (cell13058 i).lower) ≤ 1 ∧
    energyUpper 13058 (gMinus 13058) (BstLean.Part211.gPlus 13058)
      (finiteEnergy 13058 13058 0.011) (1 - (cell13058 i).lower) ≤
      (cell13058 i).energy := by
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
      have E := BstLean.Part269.S28.uniformEnergy10 (n := 13058) (by norm_num)
        (q := 1 - (cell13058 ⟨10,by decide⟩).lower)
        (by norm_num [cell13058]) (by norm_num [cell13058])
      exact ⟨E.1,E.2.trans (by norm_num [cell13058])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy11 (n := 13058) (by norm_num)
        (q := 1 - (cell13058 ⟨11,by decide⟩).lower)
        (by norm_num [cell13058]) (by norm_num [cell13058])
      exact ⟨E.1,E.2.trans (by norm_num [cell13058])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy12 (n := 13058) (by norm_num)
        (q := 1 - (cell13058 ⟨12,by decide⟩).lower)
        (by norm_num [cell13058]) (by norm_num [cell13058])
      exact ⟨E.1,E.2.trans (by norm_num [cell13058])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy13 (n := 13058) (by norm_num)
        (q := 1 - (cell13058 ⟨13,by decide⟩).lower)
        (by norm_num [cell13058]) (by norm_num [cell13058])
      exact ⟨E.1,E.2.trans (by norm_num [cell13058])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy14 (n := 13058) (by norm_num)
        (q := 1 - (cell13058 ⟨14,by decide⟩).lower)
        (by norm_num [cell13058]) (by norm_num [cell13058])
      exact ⟨E.1,E.2.trans (by norm_num [cell13058])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy15 (n := 13058) (by norm_num)
        (q := 1 - (cell13058 ⟨15,by decide⟩).lower)
        (by norm_num [cell13058]) (by norm_num [cell13058])
      exact ⟨E.1,E.2.trans (by norm_num [cell13058])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy16 (n := 13058) (by norm_num)
        (q := 1 - (cell13058 ⟨16,by decide⟩).lower)
        (by norm_num [cell13058]) (by norm_num [cell13058])
      exact ⟨E.1,E.2.trans (by norm_num [cell13058])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy17 (n := 13058) (by norm_num)
        (q := 1 - (cell13058 ⟨17,by decide⟩).lower)
        (by norm_num [cell13058]) (by norm_num [cell13058])
      exact ⟨E.1,E.2.trans (by norm_num [cell13058])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy18 (n := 13058) (by norm_num)
        (q := 1 - (cell13058 ⟨18,by decide⟩).lower)
        (by norm_num [cell13058]) (by norm_num [cell13058])
      exact ⟨E.1,E.2.trans (by norm_num [cell13058])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy19 (n := 13058) (by norm_num)
        (q := 1 - (cell13058 ⟨19,by decide⟩).lower)
        (by norm_num [cell13058]) (by norm_num [cell13058])
      exact ⟨E.1,E.2.trans (by norm_num [cell13058])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy20 (n := 13058) (by norm_num)
        (q := 1 - (cell13058 ⟨20,by decide⟩).lower)
        (by norm_num [cell13058]) (by norm_num [cell13058])
      exact ⟨E.1,E.2.trans (by norm_num [cell13058])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy21 (n := 13058) (by norm_num)
        (q := 1 - (cell13058 ⟨21,by decide⟩).lower)
        (by norm_num [cell13058]) (by norm_num [cell13058])
      exact ⟨E.1,E.2.trans (by norm_num [cell13058])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy22 (n := 13058) (by norm_num)
        (q := 1 - (cell13058 ⟨22,by decide⟩).lower)
        (by norm_num [cell13058]) (by norm_num [cell13058])
      exact ⟨E.1,E.2.trans (by norm_num [cell13058])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy23 (n := 13058) (by norm_num)
        (q := 1 - (cell13058 ⟨23,by decide⟩).lower)
        (by norm_num [cell13058]) (by norm_num [cell13058])
      exact ⟨E.1,E.2.trans (by norm_num [cell13058])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy24 (n := 13058) (by norm_num)
        (q := 1 - (cell13058 ⟨24,by decide⟩).lower)
        (by norm_num [cell13058]) (by norm_num [cell13058])
      exact ⟨E.1,E.2.trans (by norm_num [cell13058])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy25 (n := 13058) (by norm_num)
        (q := 1 - (cell13058 ⟨25,by decide⟩).lower)
        (by norm_num [cell13058]) (by norm_num [cell13058])
      exact ⟨E.1,E.2.trans (by norm_num [cell13058])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy26 (n := 13058) (by norm_num)
        (q := 1 - (cell13058 ⟨26,by decide⟩).lower)
        (by norm_num [cell13058]) (by norm_num [cell13058])
      exact ⟨E.1,E.2.trans (by norm_num [cell13058])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy27 (n := 13058) (by norm_num)
        (q := 1 - (cell13058 ⟨27,by decide⟩).lower)
        (by norm_num [cell13058]) (by norm_num [cell13058])
      exact ⟨E.1,E.2.trans (by norm_num [cell13058])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy28 (n := 13058) (by norm_num)
        (q := 1 - (cell13058 ⟨28,by decide⟩).lower)
        (by norm_num [cell13058]) (by norm_num [cell13058])
      exact ⟨E.1,E.2.trans (by norm_num [cell13058])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy29 (n := 13058) (by norm_num)
        (q := 1 - (cell13058 ⟨29,by decide⟩).lower)
        (by norm_num [cell13058]) (by norm_num [cell13058])
      exact ⟨E.1,E.2.trans (by norm_num [cell13058])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy30 (n := 13058) (by norm_num)
        (q := 1 - (cell13058 ⟨30,by decide⟩).lower)
        (by norm_num [cell13058]) (by norm_num [cell13058])
      exact ⟨E.1,E.2.trans (by norm_num [cell13058])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy31 (n := 13058) (by norm_num)
        (q := 1 - (cell13058 ⟨31,by decide⟩).lower)
        (by norm_num [cell13058]) (by norm_num [cell13058])
      exact ⟨E.1,E.2.trans (by norm_num [cell13058])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy32 (n := 13058) (by norm_num)
        (q := 1 - (cell13058 ⟨32,by decide⟩).lower)
        (by norm_num [cell13058]) (by norm_num [cell13058])
      exact ⟨E.1,E.2.trans (by norm_num [cell13058])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy33 (n := 13058) (by norm_num)
        (q := 1 - (cell13058 ⟨33,by decide⟩).lower)
        (by norm_num [cell13058]) (by norm_num [cell13058])
      exact ⟨E.1,E.2.trans (by norm_num [cell13058])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy34 (n := 13058) (by norm_num)
        (q := 1 - (cell13058 ⟨34,by decide⟩).lower)
        (by norm_num [cell13058]) (by norm_num [cell13058])
      exact ⟨E.1,E.2.trans (by norm_num [cell13058])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy35 (n := 13058) (by norm_num)
        (q := 1 - (cell13058 ⟨35,by decide⟩).lower)
        (by norm_num [cell13058]) (by norm_num [cell13058])
      exact ⟨E.1,E.2.trans (by norm_num [cell13058])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy36 (n := 13058) (by norm_num)
        (q := 1 - (cell13058 ⟨36,by decide⟩).lower)
        (by norm_num [cell13058]) (by norm_num [cell13058])
      exact ⟨E.1,E.2.trans (by norm_num [cell13058])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy37 (n := 13058) (by norm_num)
        (q := 1 - (cell13058 ⟨37,by decide⟩).lower)
        (by norm_num [cell13058]) (by norm_num [cell13058])
      exact ⟨E.1,E.2.trans (by norm_num [cell13058])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy38 (n := 13058) (by norm_num)
        (q := 1 - (cell13058 ⟨38,by decide⟩).lower)
        (by norm_num [cell13058]) (by norm_num [cell13058])
      exact ⟨E.1,E.2.trans (by norm_num [cell13058])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy39 (n := 13058) (by norm_num)
        (q := 1 - (cell13058 ⟨39,by decide⟩).lower)
        (by norm_num [cell13058]) (by norm_num [cell13058])
      exact ⟨E.1,E.2.trans (by norm_num [cell13058])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy40 (n := 13058) (by norm_num)
        (q := 1 - (cell13058 ⟨40,by decide⟩).lower)
        (by norm_num [cell13058]) (by norm_num [cell13058])
      exact ⟨E.1,E.2.trans (by norm_num [cell13058])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy41 (n := 13058) (by norm_num)
        (q := 1 - (cell13058 ⟨41,by decide⟩).lower)
        (by norm_num [cell13058]) (by norm_num [cell13058])
      exact ⟨E.1,E.2.trans (by norm_num [cell13058])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy42 (n := 13058) (by norm_num)
        (q := 1 - (cell13058 ⟨42,by decide⟩).lower)
        (by norm_num [cell13058]) (by norm_num [cell13058])
      exact ⟨E.1,E.2.trans (by norm_num [cell13058])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy43 (n := 13058) (by norm_num)
        (q := 1 - (cell13058 ⟨43,by decide⟩).lower)
        (by norm_num [cell13058]) (by norm_num [cell13058])
      exact ⟨E.1,E.2.trans (by norm_num [cell13058])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy44 (n := 13058) (by norm_num)
        (q := 1 - (cell13058 ⟨44,by decide⟩).lower)
        (by norm_num [cell13058]) (by norm_num [cell13058])
      exact ⟨E.1,E.2.trans (by norm_num [cell13058])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy45 (n := 13058) (by norm_num)
        (q := 1 - (cell13058 ⟨45,by decide⟩).lower)
        (by norm_num [cell13058]) (by norm_num [cell13058])
      exact ⟨E.1,E.2.trans (by norm_num [cell13058])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy46 (n := 13058) (by norm_num)
        (q := 1 - (cell13058 ⟨46,by decide⟩).lower)
        (by norm_num [cell13058]) (by norm_num [cell13058])
      exact ⟨E.1,E.2.trans (by norm_num [cell13058])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy47 (n := 13058) (by norm_num)
        (q := 1 - (cell13058 ⟨47,by decide⟩).lower)
        (by norm_num [cell13058]) (by norm_num [cell13058])
      exact ⟨E.1,E.2.trans (by norm_num [cell13058])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy48 (n := 13058) (by norm_num)
        (q := 1 - (cell13058 ⟨48,by decide⟩).lower)
        (by norm_num [cell13058]) (by norm_num [cell13058])
      exact ⟨E.1,E.2.trans (by norm_num [cell13058])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy49 (n := 13058) (by norm_num)
        (q := 1 - (cell13058 ⟨49,by decide⟩).lower)
        (by norm_num [cell13058]) (by norm_num [cell13058])
      exact ⟨E.1,E.2.trans (by norm_num [cell13058])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy50 (n := 13058) (by norm_num)
        (q := 1 - (cell13058 ⟨50,by decide⟩).lower)
        (by norm_num [cell13058]) (by norm_num [cell13058])
      exact ⟨E.1,E.2.trans (by norm_num [cell13058])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy51 (n := 13058) (by norm_num)
        (q := 1 - (cell13058 ⟨51,by decide⟩).lower)
        (by norm_num [cell13058]) (by norm_num [cell13058])
      exact ⟨E.1,E.2.trans (by norm_num [cell13058])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy52 (n := 13058) (by norm_num)
        (q := 1 - (cell13058 ⟨52,by decide⟩).lower)
        (by norm_num [cell13058]) (by norm_num [cell13058])
      exact ⟨E.1,E.2.trans (by norm_num [cell13058])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13058

/-! Source-cell containment and simple scalar guards at 13058. -/
namespace BstLean.Part269.N13058
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13058)
open BstLean.Part268 (cell13058)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13058 ⟨10,by decide⟩).lower ∧ (cell13058 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13058 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13058 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13058 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13058 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13058 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13058,cell13058,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13058 ⟨11,by decide⟩).lower ∧ (cell13058 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13058 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13058 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13058 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13058 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13058 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13058,cell13058,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13058 ⟨12,by decide⟩).lower ∧ (cell13058 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13058 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13058 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13058 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13058 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13058 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13058,cell13058,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13058 ⟨13,by decide⟩).lower ∧ (cell13058 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13058 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13058 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13058 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13058 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13058 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13058,cell13058,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13058 ⟨14,by decide⟩).lower ∧ (cell13058 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13058 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13058 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13058 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13058 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13058 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13058,cell13058,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13058 ⟨15,by decide⟩).lower ∧ (cell13058 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13058 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13058 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13058 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13058 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13058 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13058,cell13058,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13058 ⟨16,by decide⟩).lower ∧ (cell13058 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13058 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13058 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13058 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13058 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13058 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13058,cell13058,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13058 ⟨17,by decide⟩).lower ∧ (cell13058 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13058 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13058 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13058 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13058 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13058 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13058,cell13058,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13058 ⟨18,by decide⟩).lower ∧ (cell13058 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13058 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13058 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13058 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13058 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13058 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13058,cell13058,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13058 ⟨19,by decide⟩).lower ∧ (cell13058 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13058 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13058 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13058 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13058 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13058 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13058,cell13058,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13058 ⟨20,by decide⟩).lower ∧ (cell13058 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13058 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13058 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13058 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13058 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13058 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13058,cell13058,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13058 ⟨21,by decide⟩).lower ∧ (cell13058 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13058 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13058 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13058 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13058 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13058 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13058,cell13058,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13058 ⟨22,by decide⟩).lower ∧ (cell13058 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13058 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13058 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13058 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13058 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13058 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13058,cell13058,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13058 ⟨23,by decide⟩).lower ∧ (cell13058 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13058 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13058 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13058 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13058 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13058 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13058,cell13058,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13058 ⟨24,by decide⟩).lower ∧ (cell13058 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13058 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13058 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13058 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13058 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13058 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13058,cell13058,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13058 ⟨25,by decide⟩).lower ∧ (cell13058 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13058 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13058 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13058 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13058 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13058 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13058,cell13058,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13058 ⟨26,by decide⟩).lower ∧ (cell13058 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13058 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13058 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13058 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13058 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13058 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13058,cell13058,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13058 ⟨27,by decide⟩).lower ∧ (cell13058 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13058 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13058 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13058 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13058 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13058 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13058,cell13058,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13058 ⟨28,by decide⟩).lower ∧ (cell13058 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13058 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13058 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13058 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13058 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13058 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13058,cell13058,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13058 ⟨29,by decide⟩).lower ∧ (cell13058 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13058 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13058 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13058 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13058 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13058 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13058,cell13058,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13058 ⟨30,by decide⟩).lower ∧ (cell13058 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13058 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13058 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13058 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13058 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13058 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13058,cell13058,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13058 ⟨31,by decide⟩).lower ∧ (cell13058 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13058 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13058 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13058 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13058 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13058 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13058,cell13058,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13058 ⟨32,by decide⟩).lower ∧ (cell13058 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13058 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13058 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13058 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13058 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13058 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13058,cell13058,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13058 ⟨33,by decide⟩).lower ∧ (cell13058 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13058 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13058 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13058 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13058 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13058 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13058,cell13058,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13058 ⟨34,by decide⟩).lower ∧ (cell13058 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13058 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13058 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13058 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13058 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13058 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13058,cell13058,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13058 ⟨35,by decide⟩).lower ∧ (cell13058 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13058 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13058 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13058 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13058 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13058 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13058,cell13058,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13058 ⟨36,by decide⟩).lower ∧ (cell13058 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13058 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13058 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13058 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13058 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13058 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13058,cell13058,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13058 ⟨37,by decide⟩).lower ∧ (cell13058 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13058 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13058 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13058 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13058 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13058 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13058,cell13058,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13058 ⟨38,by decide⟩).lower ∧ (cell13058 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13058 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13058 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13058 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13058 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13058 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13058,cell13058,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13058 ⟨39,by decide⟩).lower ∧ (cell13058 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13058 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13058 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13058 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13058 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13058 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13058,cell13058,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13058 ⟨40,by decide⟩).lower ∧ (cell13058 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13058 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13058 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13058 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13058 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13058 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13058,cell13058,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13058 ⟨41,by decide⟩).lower ∧ (cell13058 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13058 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13058 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13058 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13058 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13058 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13058,cell13058,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13058 ⟨42,by decide⟩).lower ∧ (cell13058 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13058 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13058 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13058 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13058 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13058 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13058,cell13058,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13058 ⟨43,by decide⟩).lower ∧ (cell13058 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13058 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13058 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13058 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13058 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13058 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13058,cell13058,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13058 ⟨44,by decide⟩).lower ∧ (cell13058 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13058 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13058 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13058 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13058 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13058 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13058,cell13058,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13058 ⟨45,by decide⟩).lower ∧ (cell13058 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13058 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13058 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13058 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13058 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13058 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13058,cell13058,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13058 ⟨46,by decide⟩).lower ∧ (cell13058 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13058 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13058 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13058 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13058 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13058 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13058,cell13058,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13058 ⟨47,by decide⟩).lower ∧ (cell13058 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13058 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13058 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13058 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13058 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13058 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13058,cell13058,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13058 ⟨48,by decide⟩).lower ∧ (cell13058 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13058 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13058 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13058 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13058 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13058 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13058,cell13058,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13058 ⟨49,by decide⟩).lower ∧ (cell13058 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13058 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13058 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13058 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13058 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13058 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13058,cell13058,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13058 ⟨50,by decide⟩).lower ∧ (cell13058 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13058 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13058 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13058 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13058 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13058 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13058,cell13058,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13058 ⟨51,by decide⟩).lower ∧ (cell13058 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13058 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13058 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13058 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13058 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13058 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13058,cell13058,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13058 ⟨52,by decide⟩).lower ∧ (cell13058 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13058 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13058 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13058 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13058 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13058 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13058,cell13058,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13058 i).lower ∧
    (cell13058 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13058 i).upper ≤ (0.532 : ℝ) ∧
    (cell13058 i).centre ≤ (0.1 : ℝ) ∧ (cell13058 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13058 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13058 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13058

/-! The local source numeric instances at 13058 have no network premises. -/
namespace BstLean.Part269.N13058
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13058)
open BstLean.Part268 (cell13058)

noncomputable def sourceNumerics13058 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13058 (cell13058 i)
      scalarRow13058.M scalarRow13058.H scalarRow13058.xi := by
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
    energy_allowance := scalarRow13058.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13058]
    centre_nonneg := (scalarRow13058.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D28.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13058])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13058
/-! Actual 13059 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13059
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13059 ≤ (1.035309283017 : ℝ) := by
  have hr : (114.275981728445 : ℝ) ≤ √(13059 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.275981728445 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13059 13059 (11 / 1000) ≤
    (0.008364722960 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13059) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.275981728445 : ℝ) ≤ √(13059 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13059)
  have hdiv : K / √(13059 : ℝ) ≤ K / 114.275981728445 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.275981728445 ≤ (0.008364722960 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13059.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13059 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13059 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13059 := gPlus_lower 13059
end BstLean.Part269.N13059

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13059
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035309283016 : ℝ) ≤ wn 13059 := by
  have hn : √(13059 : ℝ) ≤ 114.275981728446 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13059 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.275981728446 ≤ 2 / √(13059 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000244838278 : ℝ) ≤ rhoBar 13059 BstLean.Part154.csC ∧
    rhoBar 13059 BstLean.Part154.csC ≤ 0.000244838658 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035309283016 : ℝ) / (1.295212 * 13059) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035309283017 : ℝ) / (1.29521 * 13059) := by gcongr
      _ ≤ (0.000244838658 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13059 BstLean.Part154.csC) ≤ 0.000979414578 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13059 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13059 BstLean.Part154.csC) (piBar (rhoBar 13059 BstLean.Part154.csC)) ≤ 0.000187009175 ∧
    cc1 (rhoBar 13059 BstLean.Part154.csC) (piBar (rhoBar 13059 BstLean.Part154.csC)) ≤ 0.000118995230 ∧
    cc2 (rhoBar 13059 BstLean.Part154.csC) ≤ 0.000069077704 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13059 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13059 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13059 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13059 BstLean.Part154.csC * nuR (rhoBar 13059 BstLean.Part154.csC)) ≤ 0.000489692303 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000244838658 : ℝ) * 0.000979414578 := by gcongr
      _ ≤ (0.000489692303 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13059 BstLean.Part154.csC) * nuR (rhoBar 13059 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000979414578 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13059 BstLean.Part154.csC) * rhoBar 13059 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000244838658 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000244838658 / 2 + 0.399 * 0.000979414578 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000187009175 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000489692303 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118995230 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000244838658 / 1.414213562 := by gcongr
      _ ≤ (0.000069077704 : ℝ) := by norm_num

end BstLean.Part269.N13059

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13059
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13059 BstLean.Part154.csC) (piBar (rhoBar 13059 BstLean.Part154.csC)) ≤ 1.51029E-7 := by
  have hr0 : 0 ≤ rhoBar 13059 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13059 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13059 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13059 BstLean.Part154.csC) (piBar (rhoBar 13059 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13059 BstLean.Part154.csC) (piBar (rhoBar 13059 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13059 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000187009175 : ℝ) ^ 2 + 0.000118995230 ^ 2 + 3 * 0.000069077704 ^ 2 +
        2 * 0.797885 * 0.000187009175 * 0.000118995230 + 2 * 0.000187009175 * 0.000069077704 +
        4 * 0.797885 * 0.000118995230 * 0.000069077704 := by gcongr
    _ ≤ (1.51029E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13059 BstLean.Part154.csC Θ ≤ 0.002554530721 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13059 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13059 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13059 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13059 BstLean.Part154.csC) (piBar (rhoBar 13059 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13059 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035309283017 * 1.51029E-7 / (0.000244838278 : ℝ) := by gcongr
    _ ≤ 0.002554530721 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13059 BstLean.Part154.csC Θ ≤ 0.002833027513 + 0.000645491167 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13059 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13059 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13059 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035309283017 : ℝ) * ((2 * Θ * 0.000244838658 +
        (6863 / 10000) * 0.000244838658 * 13059 * 0.000979414578) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002833027513 + 0.000645491167 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13059 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13059 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13059 0.011 Θ ∧ gammaRatio 13059 0.011 Θ ≤ 0.000084169199 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13059 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035309283017 : ℝ) * 0.525 / ((1 - 0.011) * 13059) := by gcongr
      _ ≤ (0.000084169199 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13059 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13059 0.011 Θ) :=
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
    badAllowance 13059 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000383749387 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13059 BstLean.Part154.csC) 1.22 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 2 (rhoBar 13059 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13059 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13059 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13059 0.011 Θ) 1.12 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 1 (gammaRatio 13059 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13059 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13059 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13059 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13059 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035309283017 : ℝ) * 13059 *
        (1.3781E-8 / 1.1045361 + 1.6832E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000383749387 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13059 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003216776900 + 0.003200021888 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13059

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13059
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13059 BstLean.Part154.csC) (piBar (rhoBar 13059 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13059 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13059 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13059 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13059 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13059 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13059 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13059 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13059 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13059 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13059 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13059 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13059 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13059 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13059 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051750104188 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13059) ≤ 0.010450468795 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13059 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035309283017)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010450468795 + 2 * 0.737676 / 13059) := by gcongr
    _ ≤ (0.051750104188 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13059 12 ≤ 0.0015 := by
  exact BstLean.Part269.S28.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13059

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13059
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560519357025 : ℝ) ≤ plow 13059 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13059) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052403388392)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001341128629) : eMP 13059 0.011 xi bn ≤ 0.001155064978 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13059 : ℝ) * (1 - 0.011))) ≤ 0.000571159061 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001341128629 / (13059 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000571159061 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000571159061 : ℝ) + 3.141593 * 0.052403388392 / (13059 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001155064978 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052403388392)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001341128629) : PiBarMP 13059 12 0.011 xi bn ≤ 0.158997160629 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13059 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036621423089 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.645725832518 : ℝ) ≤ √((13059 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.275981728445 : ℝ) ≤ √(13059 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13059) ≤ 0.121918954903 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036621423089 + 0.052403388392 * 1.772454 / (2 * (113.645725832518 : ℝ))) * (1 + 0.001155064978) +
        8 / (13059 * 114.275981728445) + 0.121918954903 := by gcongr
    _ ≤ (0.158997160629 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052403388392)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001341128629) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280667968044) :
    parallelOracle 13059 0.011 xi bn cd ≤ 0.159960411256 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13059 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13059 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560519357025 : ℝ) ≤ plow 13059 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.275981728445 : ℝ) ≤ √(13059 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280667968044 : ℝ) / (2 * 0.560519357025 * 114.275981728445)) * 0.158997160629 +
        0.280667968044 ^ 2 / (2 * 0.560519357025 * 114.275981728445) := by gcongr
    _ ≤ (0.159960411256 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052403388392) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001341128629)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280667968044) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13059 13059 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560519357025 : ℝ) ≤ plow 13059 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.275981728445 : ℝ) ≤ √(13059 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13059 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13059 Θ 1.22 ≤ 0.011604367602 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.275981728445 := by gcongr <;> linarith
      _ ≤ (0.011604367602 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13059 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13059 13059 0.011 ≤ 0.008364722960 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13059 13059 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13059 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13059 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13059 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13059 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159960411256 + 0.011604367602 + (0.008364722960 : ℝ) *
        (1 + 2 * (0.280667968044 + 0.011604367602) / (0.560519357025 * 114.275981728445))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13059]

end BstLean.Part269.N13059

/-! The original eight local profiles supply actual 13059 moment certificates. -/
namespace BstLean.Part269.N13059
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13059 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13059 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13059 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052403388392 ∧
    0 ≤ bN 13059 BstLean.Part154.csC (groupTheta g) ∧ bN 13059 BstLean.Part154.csC (groupTheta g) ≤ 0.001341128629 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13059 13059 0.011
      (momentAllowance 13059 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13059 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13059 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13059 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13059 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13059 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228917863856 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13059 0.011
      (momentAllowance 13059 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13059 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13059
/-! The actual computed-centre upper energy formula at 13059. -/
namespace BstLean.Part269.N13059
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13059

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13059
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13059)
open BstLean.Part268 (cell13059)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084506997066
  | 2 => 0.085433679675
  | 3 => 0.086356272666
  | 4 => 0.087275670172
  | 5 => 0.088192968892
  | 6 => 0.089109500039
  | 7 => 0.090026864672
  | 8 => 0.090946972477
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13059 13059 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13059 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003218831707 + 0.003202305177 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S28.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13059

/-! Actual upper energy certificates on all 43 source endpoints at 13059. -/
namespace BstLean.Part269.N13059
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13059)
open BstLean.Part268 (cell13059)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13059 (gMinus 13059) (1 - (cell13059 i).lower) ≤ 1 ∧
    energyUpper 13059 (gMinus 13059) (BstLean.Part211.gPlus 13059)
      (finiteEnergy 13059 13059 0.011) (1 - (cell13059 i).lower) ≤
      (cell13059 i).energy := by
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
      have E := BstLean.Part269.S28.uniformEnergy10 (n := 13059) (by norm_num)
        (q := 1 - (cell13059 ⟨10,by decide⟩).lower)
        (by norm_num [cell13059]) (by norm_num [cell13059])
      exact ⟨E.1,E.2.trans (by norm_num [cell13059])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy11 (n := 13059) (by norm_num)
        (q := 1 - (cell13059 ⟨11,by decide⟩).lower)
        (by norm_num [cell13059]) (by norm_num [cell13059])
      exact ⟨E.1,E.2.trans (by norm_num [cell13059])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy12 (n := 13059) (by norm_num)
        (q := 1 - (cell13059 ⟨12,by decide⟩).lower)
        (by norm_num [cell13059]) (by norm_num [cell13059])
      exact ⟨E.1,E.2.trans (by norm_num [cell13059])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy13 (n := 13059) (by norm_num)
        (q := 1 - (cell13059 ⟨13,by decide⟩).lower)
        (by norm_num [cell13059]) (by norm_num [cell13059])
      exact ⟨E.1,E.2.trans (by norm_num [cell13059])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy14 (n := 13059) (by norm_num)
        (q := 1 - (cell13059 ⟨14,by decide⟩).lower)
        (by norm_num [cell13059]) (by norm_num [cell13059])
      exact ⟨E.1,E.2.trans (by norm_num [cell13059])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy15 (n := 13059) (by norm_num)
        (q := 1 - (cell13059 ⟨15,by decide⟩).lower)
        (by norm_num [cell13059]) (by norm_num [cell13059])
      exact ⟨E.1,E.2.trans (by norm_num [cell13059])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy16 (n := 13059) (by norm_num)
        (q := 1 - (cell13059 ⟨16,by decide⟩).lower)
        (by norm_num [cell13059]) (by norm_num [cell13059])
      exact ⟨E.1,E.2.trans (by norm_num [cell13059])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy17 (n := 13059) (by norm_num)
        (q := 1 - (cell13059 ⟨17,by decide⟩).lower)
        (by norm_num [cell13059]) (by norm_num [cell13059])
      exact ⟨E.1,E.2.trans (by norm_num [cell13059])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy18 (n := 13059) (by norm_num)
        (q := 1 - (cell13059 ⟨18,by decide⟩).lower)
        (by norm_num [cell13059]) (by norm_num [cell13059])
      exact ⟨E.1,E.2.trans (by norm_num [cell13059])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy19 (n := 13059) (by norm_num)
        (q := 1 - (cell13059 ⟨19,by decide⟩).lower)
        (by norm_num [cell13059]) (by norm_num [cell13059])
      exact ⟨E.1,E.2.trans (by norm_num [cell13059])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy20 (n := 13059) (by norm_num)
        (q := 1 - (cell13059 ⟨20,by decide⟩).lower)
        (by norm_num [cell13059]) (by norm_num [cell13059])
      exact ⟨E.1,E.2.trans (by norm_num [cell13059])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy21 (n := 13059) (by norm_num)
        (q := 1 - (cell13059 ⟨21,by decide⟩).lower)
        (by norm_num [cell13059]) (by norm_num [cell13059])
      exact ⟨E.1,E.2.trans (by norm_num [cell13059])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy22 (n := 13059) (by norm_num)
        (q := 1 - (cell13059 ⟨22,by decide⟩).lower)
        (by norm_num [cell13059]) (by norm_num [cell13059])
      exact ⟨E.1,E.2.trans (by norm_num [cell13059])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy23 (n := 13059) (by norm_num)
        (q := 1 - (cell13059 ⟨23,by decide⟩).lower)
        (by norm_num [cell13059]) (by norm_num [cell13059])
      exact ⟨E.1,E.2.trans (by norm_num [cell13059])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy24 (n := 13059) (by norm_num)
        (q := 1 - (cell13059 ⟨24,by decide⟩).lower)
        (by norm_num [cell13059]) (by norm_num [cell13059])
      exact ⟨E.1,E.2.trans (by norm_num [cell13059])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy25 (n := 13059) (by norm_num)
        (q := 1 - (cell13059 ⟨25,by decide⟩).lower)
        (by norm_num [cell13059]) (by norm_num [cell13059])
      exact ⟨E.1,E.2.trans (by norm_num [cell13059])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy26 (n := 13059) (by norm_num)
        (q := 1 - (cell13059 ⟨26,by decide⟩).lower)
        (by norm_num [cell13059]) (by norm_num [cell13059])
      exact ⟨E.1,E.2.trans (by norm_num [cell13059])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy27 (n := 13059) (by norm_num)
        (q := 1 - (cell13059 ⟨27,by decide⟩).lower)
        (by norm_num [cell13059]) (by norm_num [cell13059])
      exact ⟨E.1,E.2.trans (by norm_num [cell13059])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy28 (n := 13059) (by norm_num)
        (q := 1 - (cell13059 ⟨28,by decide⟩).lower)
        (by norm_num [cell13059]) (by norm_num [cell13059])
      exact ⟨E.1,E.2.trans (by norm_num [cell13059])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy29 (n := 13059) (by norm_num)
        (q := 1 - (cell13059 ⟨29,by decide⟩).lower)
        (by norm_num [cell13059]) (by norm_num [cell13059])
      exact ⟨E.1,E.2.trans (by norm_num [cell13059])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy30 (n := 13059) (by norm_num)
        (q := 1 - (cell13059 ⟨30,by decide⟩).lower)
        (by norm_num [cell13059]) (by norm_num [cell13059])
      exact ⟨E.1,E.2.trans (by norm_num [cell13059])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy31 (n := 13059) (by norm_num)
        (q := 1 - (cell13059 ⟨31,by decide⟩).lower)
        (by norm_num [cell13059]) (by norm_num [cell13059])
      exact ⟨E.1,E.2.trans (by norm_num [cell13059])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy32 (n := 13059) (by norm_num)
        (q := 1 - (cell13059 ⟨32,by decide⟩).lower)
        (by norm_num [cell13059]) (by norm_num [cell13059])
      exact ⟨E.1,E.2.trans (by norm_num [cell13059])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy33 (n := 13059) (by norm_num)
        (q := 1 - (cell13059 ⟨33,by decide⟩).lower)
        (by norm_num [cell13059]) (by norm_num [cell13059])
      exact ⟨E.1,E.2.trans (by norm_num [cell13059])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy34 (n := 13059) (by norm_num)
        (q := 1 - (cell13059 ⟨34,by decide⟩).lower)
        (by norm_num [cell13059]) (by norm_num [cell13059])
      exact ⟨E.1,E.2.trans (by norm_num [cell13059])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy35 (n := 13059) (by norm_num)
        (q := 1 - (cell13059 ⟨35,by decide⟩).lower)
        (by norm_num [cell13059]) (by norm_num [cell13059])
      exact ⟨E.1,E.2.trans (by norm_num [cell13059])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy36 (n := 13059) (by norm_num)
        (q := 1 - (cell13059 ⟨36,by decide⟩).lower)
        (by norm_num [cell13059]) (by norm_num [cell13059])
      exact ⟨E.1,E.2.trans (by norm_num [cell13059])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy37 (n := 13059) (by norm_num)
        (q := 1 - (cell13059 ⟨37,by decide⟩).lower)
        (by norm_num [cell13059]) (by norm_num [cell13059])
      exact ⟨E.1,E.2.trans (by norm_num [cell13059])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy38 (n := 13059) (by norm_num)
        (q := 1 - (cell13059 ⟨38,by decide⟩).lower)
        (by norm_num [cell13059]) (by norm_num [cell13059])
      exact ⟨E.1,E.2.trans (by norm_num [cell13059])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy39 (n := 13059) (by norm_num)
        (q := 1 - (cell13059 ⟨39,by decide⟩).lower)
        (by norm_num [cell13059]) (by norm_num [cell13059])
      exact ⟨E.1,E.2.trans (by norm_num [cell13059])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy40 (n := 13059) (by norm_num)
        (q := 1 - (cell13059 ⟨40,by decide⟩).lower)
        (by norm_num [cell13059]) (by norm_num [cell13059])
      exact ⟨E.1,E.2.trans (by norm_num [cell13059])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy41 (n := 13059) (by norm_num)
        (q := 1 - (cell13059 ⟨41,by decide⟩).lower)
        (by norm_num [cell13059]) (by norm_num [cell13059])
      exact ⟨E.1,E.2.trans (by norm_num [cell13059])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy42 (n := 13059) (by norm_num)
        (q := 1 - (cell13059 ⟨42,by decide⟩).lower)
        (by norm_num [cell13059]) (by norm_num [cell13059])
      exact ⟨E.1,E.2.trans (by norm_num [cell13059])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy43 (n := 13059) (by norm_num)
        (q := 1 - (cell13059 ⟨43,by decide⟩).lower)
        (by norm_num [cell13059]) (by norm_num [cell13059])
      exact ⟨E.1,E.2.trans (by norm_num [cell13059])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy44 (n := 13059) (by norm_num)
        (q := 1 - (cell13059 ⟨44,by decide⟩).lower)
        (by norm_num [cell13059]) (by norm_num [cell13059])
      exact ⟨E.1,E.2.trans (by norm_num [cell13059])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy45 (n := 13059) (by norm_num)
        (q := 1 - (cell13059 ⟨45,by decide⟩).lower)
        (by norm_num [cell13059]) (by norm_num [cell13059])
      exact ⟨E.1,E.2.trans (by norm_num [cell13059])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy46 (n := 13059) (by norm_num)
        (q := 1 - (cell13059 ⟨46,by decide⟩).lower)
        (by norm_num [cell13059]) (by norm_num [cell13059])
      exact ⟨E.1,E.2.trans (by norm_num [cell13059])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy47 (n := 13059) (by norm_num)
        (q := 1 - (cell13059 ⟨47,by decide⟩).lower)
        (by norm_num [cell13059]) (by norm_num [cell13059])
      exact ⟨E.1,E.2.trans (by norm_num [cell13059])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy48 (n := 13059) (by norm_num)
        (q := 1 - (cell13059 ⟨48,by decide⟩).lower)
        (by norm_num [cell13059]) (by norm_num [cell13059])
      exact ⟨E.1,E.2.trans (by norm_num [cell13059])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy49 (n := 13059) (by norm_num)
        (q := 1 - (cell13059 ⟨49,by decide⟩).lower)
        (by norm_num [cell13059]) (by norm_num [cell13059])
      exact ⟨E.1,E.2.trans (by norm_num [cell13059])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy50 (n := 13059) (by norm_num)
        (q := 1 - (cell13059 ⟨50,by decide⟩).lower)
        (by norm_num [cell13059]) (by norm_num [cell13059])
      exact ⟨E.1,E.2.trans (by norm_num [cell13059])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy51 (n := 13059) (by norm_num)
        (q := 1 - (cell13059 ⟨51,by decide⟩).lower)
        (by norm_num [cell13059]) (by norm_num [cell13059])
      exact ⟨E.1,E.2.trans (by norm_num [cell13059])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy52 (n := 13059) (by norm_num)
        (q := 1 - (cell13059 ⟨52,by decide⟩).lower)
        (by norm_num [cell13059]) (by norm_num [cell13059])
      exact ⟨E.1,E.2.trans (by norm_num [cell13059])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13059

/-! Source-cell containment and simple scalar guards at 13059. -/
namespace BstLean.Part269.N13059
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13059)
open BstLean.Part268 (cell13059)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13059 ⟨10,by decide⟩).lower ∧ (cell13059 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13059 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13059 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13059 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13059 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13059 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13059,cell13059,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13059 ⟨11,by decide⟩).lower ∧ (cell13059 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13059 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13059 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13059 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13059 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13059 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13059,cell13059,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13059 ⟨12,by decide⟩).lower ∧ (cell13059 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13059 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13059 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13059 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13059 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13059 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13059,cell13059,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13059 ⟨13,by decide⟩).lower ∧ (cell13059 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13059 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13059 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13059 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13059 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13059 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13059,cell13059,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13059 ⟨14,by decide⟩).lower ∧ (cell13059 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13059 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13059 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13059 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13059 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13059 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13059,cell13059,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13059 ⟨15,by decide⟩).lower ∧ (cell13059 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13059 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13059 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13059 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13059 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13059 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13059,cell13059,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13059 ⟨16,by decide⟩).lower ∧ (cell13059 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13059 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13059 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13059 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13059 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13059 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13059,cell13059,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13059 ⟨17,by decide⟩).lower ∧ (cell13059 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13059 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13059 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13059 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13059 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13059 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13059,cell13059,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13059 ⟨18,by decide⟩).lower ∧ (cell13059 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13059 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13059 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13059 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13059 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13059 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13059,cell13059,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13059 ⟨19,by decide⟩).lower ∧ (cell13059 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13059 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13059 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13059 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13059 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13059 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13059,cell13059,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13059 ⟨20,by decide⟩).lower ∧ (cell13059 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13059 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13059 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13059 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13059 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13059 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13059,cell13059,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13059 ⟨21,by decide⟩).lower ∧ (cell13059 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13059 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13059 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13059 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13059 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13059 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13059,cell13059,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13059 ⟨22,by decide⟩).lower ∧ (cell13059 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13059 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13059 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13059 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13059 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13059 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13059,cell13059,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13059 ⟨23,by decide⟩).lower ∧ (cell13059 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13059 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13059 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13059 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13059 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13059 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13059,cell13059,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13059 ⟨24,by decide⟩).lower ∧ (cell13059 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13059 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13059 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13059 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13059 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13059 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13059,cell13059,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13059 ⟨25,by decide⟩).lower ∧ (cell13059 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13059 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13059 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13059 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13059 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13059 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13059,cell13059,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13059 ⟨26,by decide⟩).lower ∧ (cell13059 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13059 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13059 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13059 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13059 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13059 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13059,cell13059,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13059 ⟨27,by decide⟩).lower ∧ (cell13059 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13059 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13059 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13059 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13059 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13059 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13059,cell13059,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13059 ⟨28,by decide⟩).lower ∧ (cell13059 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13059 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13059 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13059 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13059 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13059 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13059,cell13059,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13059 ⟨29,by decide⟩).lower ∧ (cell13059 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13059 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13059 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13059 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13059 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13059 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13059,cell13059,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13059 ⟨30,by decide⟩).lower ∧ (cell13059 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13059 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13059 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13059 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13059 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13059 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13059,cell13059,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13059 ⟨31,by decide⟩).lower ∧ (cell13059 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13059 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13059 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13059 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13059 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13059 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13059,cell13059,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13059 ⟨32,by decide⟩).lower ∧ (cell13059 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13059 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13059 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13059 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13059 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13059 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13059,cell13059,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13059 ⟨33,by decide⟩).lower ∧ (cell13059 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13059 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13059 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13059 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13059 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13059 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13059,cell13059,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13059 ⟨34,by decide⟩).lower ∧ (cell13059 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13059 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13059 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13059 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13059 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13059 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13059,cell13059,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13059 ⟨35,by decide⟩).lower ∧ (cell13059 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13059 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13059 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13059 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13059 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13059 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13059,cell13059,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13059 ⟨36,by decide⟩).lower ∧ (cell13059 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13059 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13059 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13059 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13059 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13059 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13059,cell13059,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13059 ⟨37,by decide⟩).lower ∧ (cell13059 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13059 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13059 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13059 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13059 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13059 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13059,cell13059,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13059 ⟨38,by decide⟩).lower ∧ (cell13059 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13059 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13059 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13059 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13059 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13059 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13059,cell13059,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13059 ⟨39,by decide⟩).lower ∧ (cell13059 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13059 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13059 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13059 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13059 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13059 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13059,cell13059,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13059 ⟨40,by decide⟩).lower ∧ (cell13059 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13059 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13059 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13059 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13059 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13059 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13059,cell13059,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13059 ⟨41,by decide⟩).lower ∧ (cell13059 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13059 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13059 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13059 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13059 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13059 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13059,cell13059,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13059 ⟨42,by decide⟩).lower ∧ (cell13059 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13059 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13059 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13059 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13059 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13059 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13059,cell13059,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13059 ⟨43,by decide⟩).lower ∧ (cell13059 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13059 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13059 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13059 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13059 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13059 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13059,cell13059,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13059 ⟨44,by decide⟩).lower ∧ (cell13059 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13059 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13059 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13059 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13059 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13059 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13059,cell13059,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13059 ⟨45,by decide⟩).lower ∧ (cell13059 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13059 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13059 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13059 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13059 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13059 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13059,cell13059,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13059 ⟨46,by decide⟩).lower ∧ (cell13059 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13059 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13059 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13059 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13059 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13059 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13059,cell13059,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13059 ⟨47,by decide⟩).lower ∧ (cell13059 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13059 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13059 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13059 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13059 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13059 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13059,cell13059,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13059 ⟨48,by decide⟩).lower ∧ (cell13059 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13059 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13059 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13059 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13059 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13059 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13059,cell13059,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13059 ⟨49,by decide⟩).lower ∧ (cell13059 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13059 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13059 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13059 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13059 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13059 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13059,cell13059,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13059 ⟨50,by decide⟩).lower ∧ (cell13059 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13059 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13059 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13059 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13059 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13059 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13059,cell13059,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13059 ⟨51,by decide⟩).lower ∧ (cell13059 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13059 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13059 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13059 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13059 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13059 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13059,cell13059,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13059 ⟨52,by decide⟩).lower ∧ (cell13059 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13059 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13059 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13059 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13059 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13059 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13059,cell13059,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13059 i).lower ∧
    (cell13059 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13059 i).upper ≤ (0.532 : ℝ) ∧
    (cell13059 i).centre ≤ (0.1 : ℝ) ∧ (cell13059 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13059 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13059 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13059

/-! The local source numeric instances at 13059 have no network premises. -/
namespace BstLean.Part269.N13059
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13059)
open BstLean.Part268 (cell13059)

noncomputable def sourceNumerics13059 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13059 (cell13059 i)
      scalarRow13059.M scalarRow13059.H scalarRow13059.xi := by
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
    energy_allowance := scalarRow13059.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13059]
    centre_nonneg := (scalarRow13059.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D28.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13059])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13059
/-! Actual 13060 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13060
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13060 ≤ (1.035307919454 : ℝ) := by
  have hr : (114.280357017293 : ℝ) ≤ √(13060 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.280357017293 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13060 13060 (11 / 1000) ≤
    (0.008364402709 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13060) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.280357017293 : ℝ) ≤ √(13060 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13060)
  have hdiv : K / √(13060 : ℝ) ≤ K / 114.280357017293 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.280357017293 ≤ (0.008364402709 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13060.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13060 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13060 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13060 := gPlus_lower 13060
end BstLean.Part269.N13060

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13060
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035307919453 : ℝ) ≤ wn 13060 := by
  have hn : √(13060 : ℝ) ≤ 114.280357017294 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13060 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.280357017294 ≤ 2 / √(13060 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000244819209 : ℝ) ≤ rhoBar 13060 BstLean.Part154.csC ∧
    rhoBar 13060 BstLean.Part154.csC ≤ 0.000244819588 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035307919453 : ℝ) / (1.295212 * 13060) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035307919454 : ℝ) / (1.29521 * 13060) := by gcongr
      _ ≤ (0.000244819588 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13060 BstLean.Part154.csC) ≤ 0.000979338289 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13060 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13060 BstLean.Part154.csC) (piBar (rhoBar 13060 BstLean.Part154.csC)) ≤ 0.000186994609 ∧
    cc1 (rhoBar 13060 BstLean.Part154.csC) (piBar (rhoBar 13060 BstLean.Part154.csC)) ≤ 0.000118985962 ∧
    cc2 (rhoBar 13060 BstLean.Part154.csC) ≤ 0.000069072323 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13060 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13060 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13060 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13060 BstLean.Part154.csC * nuR (rhoBar 13060 BstLean.Part154.csC)) ≤ 0.000489654161 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000244819588 : ℝ) * 0.000979338289 := by gcongr
      _ ≤ (0.000489654161 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13060 BstLean.Part154.csC) * nuR (rhoBar 13060 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000979338289 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13060 BstLean.Part154.csC) * rhoBar 13060 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000244819588 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000244819588 / 2 + 0.399 * 0.000979338289 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000186994609 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000489654161 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118985962 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000244819588 / 1.414213562 := by gcongr
      _ ≤ (0.000069072323 : ℝ) := by norm_num

end BstLean.Part269.N13060

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13060
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13060 BstLean.Part154.csC) (piBar (rhoBar 13060 BstLean.Part154.csC)) ≤ 1.51006E-7 := by
  have hr0 : 0 ≤ rhoBar 13060 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13060 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13060 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13060 BstLean.Part154.csC) (piBar (rhoBar 13060 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13060 BstLean.Part154.csC) (piBar (rhoBar 13060 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13060 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000186994609 : ℝ) ^ 2 + 0.000118985962 ^ 2 + 3 * 0.000069072323 ^ 2 +
        2 * 0.797885 * 0.000186994609 * 0.000118985962 + 2 * 0.000186994609 * 0.000069072323 +
        4 * 0.797885 * 0.000118985962 * 0.000069072323 := by gcongr
    _ ≤ (1.51006E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13060 BstLean.Part154.csC Θ ≤ 0.002554337274 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13060 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13060 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13060 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13060 BstLean.Part154.csC) (piBar (rhoBar 13060 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13060 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035307919454 * 1.51006E-7 / (0.000244819209 : ℝ) := by gcongr
    _ ≤ 0.002554337274 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13060 BstLean.Part154.csC Θ ≤ 0.002832799376 + 0.000645440041 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13060 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13060 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13060 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035307919454 : ℝ) * ((2 * Θ * 0.000244819588 +
        (6863 / 10000) * 0.000244819588 * 13060 * 0.000979338289) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002832799376 + 0.000645440041 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13060 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13060 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13060 0.011 Θ ∧ gammaRatio 13060 0.011 Θ ≤ 0.000084162644 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13060 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035307919454 : ℝ) * 0.525 / ((1 - 0.011) * 13060) := by gcongr
      _ ≤ (0.000084162644 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13060 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13060 0.011 Θ) :=
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
    badAllowance 13060 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000383749387 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13060 BstLean.Part154.csC) 1.22 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 2 (rhoBar 13060 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13060 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13060 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13060 0.011 Θ) 1.12 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 1 (gammaRatio 13060 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13060 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13060 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13060 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13060 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035307919454 : ℝ) * 13060 *
        (1.3781E-8 / 1.1045361 + 1.6832E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000383749387 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13060 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003216548763 + 0.003199777315 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13060

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13060
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13060 BstLean.Part154.csC) (piBar (rhoBar 13060 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13060 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13060 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13060 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13060 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13060 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13060 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13060 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13060 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13060 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13060 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13060 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13060 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13060 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13060 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051748101718 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13060) ≤ 0.010450068693 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13060 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035307919454)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010450068693 + 2 * 0.737676 / 13060) := by gcongr
    _ ≤ (0.051748101718 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13060 12 ≤ 0.0015 := by
  exact BstLean.Part269.S28.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13060

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13060
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560519399793 : ℝ) ≤ plow 13060 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13060) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052403031854)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001341027069) : eMP 13060 0.011 xi bn ≤ 0.001154976930 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13060 : ℝ) * (1 - 0.011))) ≤ 0.000571115568 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001341027069 / (13060 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000571115568 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000571115568 : ℝ) + 3.141593 * 0.052403031854 / (13060 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001154976930 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052403031854)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001341027069) : PiBarMP 13060 12 0.011 xi bn ≤ 0.158991082321 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13060 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036620036442 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.650076990735 : ℝ) ≤ √((13060 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.280357017293 : ℝ) ≤ √(13060 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13060) ≤ 0.121914287166 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036620036442 + 0.052403031854 * 1.772454 / (2 * (113.650076990735 : ℝ))) * (1 + 0.001154976930) +
        8 / (13060 * 114.280357017293) + 0.121914287166 := by gcongr
    _ ≤ (0.158991082321 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052403031854)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001341027069) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280665186826) :
    parallelOracle 13060 0.011 xi bn cd ≤ 0.159954267042 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13060 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13060 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560519399793 : ℝ) ≤ plow 13060 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.280357017293 : ℝ) ≤ √(13060 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280665186826 : ℝ) / (2 * 0.560519399793 * 114.280357017293)) * 0.158991082321 +
        0.280665186826 ^ 2 / (2 * 0.560519399793 * 114.280357017293) := by gcongr
    _ ≤ (0.159954267042 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052403031854) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001341027069)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280665186826) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13060 13060 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560519399793 : ℝ) ≤ plow 13060 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.280357017293 : ℝ) ≤ √(13060 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13060 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13060 Θ 1.22 ≤ 0.011603923322 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.280357017293 := by gcongr <;> linarith
      _ ≤ (0.011603923322 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13060 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13060 13060 0.011 ≤ 0.008364402709 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13060 13060 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13060 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13060 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13060 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13060 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159954267042 + 0.011603923322 + (0.008364402709 : ℝ) *
        (1 + 2 * (0.280665186826 + 0.011603923322) / (0.560519399793 * 114.280357017293))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13060]

end BstLean.Part269.N13060

/-! The original eight local profiles supply actual 13060 moment certificates. -/
namespace BstLean.Part269.N13060
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13060 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13060 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13060 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052403031854 ∧
    0 ≤ bN 13060 BstLean.Part154.csC (groupTheta g) ∧ bN 13060 BstLean.Part154.csC (groupTheta g) ≤ 0.001341027069 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13060 13060 0.011
      (momentAllowance 13060 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13060 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13060 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13060 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13060 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13060 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228917085108 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13060 0.011
      (momentAllowance 13060 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13060 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13060
/-! The actual computed-centre upper energy formula at 13060. -/
namespace BstLean.Part269.N13060
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13060

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13060
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13060)
open BstLean.Part268 (cell13060)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084504425213
  | 2 => 0.085431074894
  | 3 => 0.086353630092
  | 4 => 0.087272983791
  | 5 => 0.088190231327
  | 6 => 0.089106702315
  | 7 => 0.090023995942
  | 8 => 0.090944019726
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13060 13060 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13060 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003218831707 + 0.003202305177 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S28.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13060

/-! Actual upper energy certificates on all 43 source endpoints at 13060. -/
namespace BstLean.Part269.N13060
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13060)
open BstLean.Part268 (cell13060)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13060 (gMinus 13060) (1 - (cell13060 i).lower) ≤ 1 ∧
    energyUpper 13060 (gMinus 13060) (BstLean.Part211.gPlus 13060)
      (finiteEnergy 13060 13060 0.011) (1 - (cell13060 i).lower) ≤
      (cell13060 i).energy := by
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
      have E := BstLean.Part269.S28.uniformEnergy10 (n := 13060) (by norm_num)
        (q := 1 - (cell13060 ⟨10,by decide⟩).lower)
        (by norm_num [cell13060]) (by norm_num [cell13060])
      exact ⟨E.1,E.2.trans (by norm_num [cell13060])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy11 (n := 13060) (by norm_num)
        (q := 1 - (cell13060 ⟨11,by decide⟩).lower)
        (by norm_num [cell13060]) (by norm_num [cell13060])
      exact ⟨E.1,E.2.trans (by norm_num [cell13060])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy12 (n := 13060) (by norm_num)
        (q := 1 - (cell13060 ⟨12,by decide⟩).lower)
        (by norm_num [cell13060]) (by norm_num [cell13060])
      exact ⟨E.1,E.2.trans (by norm_num [cell13060])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy13 (n := 13060) (by norm_num)
        (q := 1 - (cell13060 ⟨13,by decide⟩).lower)
        (by norm_num [cell13060]) (by norm_num [cell13060])
      exact ⟨E.1,E.2.trans (by norm_num [cell13060])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy14 (n := 13060) (by norm_num)
        (q := 1 - (cell13060 ⟨14,by decide⟩).lower)
        (by norm_num [cell13060]) (by norm_num [cell13060])
      exact ⟨E.1,E.2.trans (by norm_num [cell13060])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy15 (n := 13060) (by norm_num)
        (q := 1 - (cell13060 ⟨15,by decide⟩).lower)
        (by norm_num [cell13060]) (by norm_num [cell13060])
      exact ⟨E.1,E.2.trans (by norm_num [cell13060])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy16 (n := 13060) (by norm_num)
        (q := 1 - (cell13060 ⟨16,by decide⟩).lower)
        (by norm_num [cell13060]) (by norm_num [cell13060])
      exact ⟨E.1,E.2.trans (by norm_num [cell13060])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy17 (n := 13060) (by norm_num)
        (q := 1 - (cell13060 ⟨17,by decide⟩).lower)
        (by norm_num [cell13060]) (by norm_num [cell13060])
      exact ⟨E.1,E.2.trans (by norm_num [cell13060])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy18 (n := 13060) (by norm_num)
        (q := 1 - (cell13060 ⟨18,by decide⟩).lower)
        (by norm_num [cell13060]) (by norm_num [cell13060])
      exact ⟨E.1,E.2.trans (by norm_num [cell13060])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy19 (n := 13060) (by norm_num)
        (q := 1 - (cell13060 ⟨19,by decide⟩).lower)
        (by norm_num [cell13060]) (by norm_num [cell13060])
      exact ⟨E.1,E.2.trans (by norm_num [cell13060])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy20 (n := 13060) (by norm_num)
        (q := 1 - (cell13060 ⟨20,by decide⟩).lower)
        (by norm_num [cell13060]) (by norm_num [cell13060])
      exact ⟨E.1,E.2.trans (by norm_num [cell13060])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy21 (n := 13060) (by norm_num)
        (q := 1 - (cell13060 ⟨21,by decide⟩).lower)
        (by norm_num [cell13060]) (by norm_num [cell13060])
      exact ⟨E.1,E.2.trans (by norm_num [cell13060])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy22 (n := 13060) (by norm_num)
        (q := 1 - (cell13060 ⟨22,by decide⟩).lower)
        (by norm_num [cell13060]) (by norm_num [cell13060])
      exact ⟨E.1,E.2.trans (by norm_num [cell13060])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy23 (n := 13060) (by norm_num)
        (q := 1 - (cell13060 ⟨23,by decide⟩).lower)
        (by norm_num [cell13060]) (by norm_num [cell13060])
      exact ⟨E.1,E.2.trans (by norm_num [cell13060])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy24 (n := 13060) (by norm_num)
        (q := 1 - (cell13060 ⟨24,by decide⟩).lower)
        (by norm_num [cell13060]) (by norm_num [cell13060])
      exact ⟨E.1,E.2.trans (by norm_num [cell13060])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy25 (n := 13060) (by norm_num)
        (q := 1 - (cell13060 ⟨25,by decide⟩).lower)
        (by norm_num [cell13060]) (by norm_num [cell13060])
      exact ⟨E.1,E.2.trans (by norm_num [cell13060])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy26 (n := 13060) (by norm_num)
        (q := 1 - (cell13060 ⟨26,by decide⟩).lower)
        (by norm_num [cell13060]) (by norm_num [cell13060])
      exact ⟨E.1,E.2.trans (by norm_num [cell13060])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy27 (n := 13060) (by norm_num)
        (q := 1 - (cell13060 ⟨27,by decide⟩).lower)
        (by norm_num [cell13060]) (by norm_num [cell13060])
      exact ⟨E.1,E.2.trans (by norm_num [cell13060])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy28 (n := 13060) (by norm_num)
        (q := 1 - (cell13060 ⟨28,by decide⟩).lower)
        (by norm_num [cell13060]) (by norm_num [cell13060])
      exact ⟨E.1,E.2.trans (by norm_num [cell13060])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy29 (n := 13060) (by norm_num)
        (q := 1 - (cell13060 ⟨29,by decide⟩).lower)
        (by norm_num [cell13060]) (by norm_num [cell13060])
      exact ⟨E.1,E.2.trans (by norm_num [cell13060])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy30 (n := 13060) (by norm_num)
        (q := 1 - (cell13060 ⟨30,by decide⟩).lower)
        (by norm_num [cell13060]) (by norm_num [cell13060])
      exact ⟨E.1,E.2.trans (by norm_num [cell13060])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy31 (n := 13060) (by norm_num)
        (q := 1 - (cell13060 ⟨31,by decide⟩).lower)
        (by norm_num [cell13060]) (by norm_num [cell13060])
      exact ⟨E.1,E.2.trans (by norm_num [cell13060])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy32 (n := 13060) (by norm_num)
        (q := 1 - (cell13060 ⟨32,by decide⟩).lower)
        (by norm_num [cell13060]) (by norm_num [cell13060])
      exact ⟨E.1,E.2.trans (by norm_num [cell13060])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy33 (n := 13060) (by norm_num)
        (q := 1 - (cell13060 ⟨33,by decide⟩).lower)
        (by norm_num [cell13060]) (by norm_num [cell13060])
      exact ⟨E.1,E.2.trans (by norm_num [cell13060])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy34 (n := 13060) (by norm_num)
        (q := 1 - (cell13060 ⟨34,by decide⟩).lower)
        (by norm_num [cell13060]) (by norm_num [cell13060])
      exact ⟨E.1,E.2.trans (by norm_num [cell13060])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy35 (n := 13060) (by norm_num)
        (q := 1 - (cell13060 ⟨35,by decide⟩).lower)
        (by norm_num [cell13060]) (by norm_num [cell13060])
      exact ⟨E.1,E.2.trans (by norm_num [cell13060])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy36 (n := 13060) (by norm_num)
        (q := 1 - (cell13060 ⟨36,by decide⟩).lower)
        (by norm_num [cell13060]) (by norm_num [cell13060])
      exact ⟨E.1,E.2.trans (by norm_num [cell13060])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy37 (n := 13060) (by norm_num)
        (q := 1 - (cell13060 ⟨37,by decide⟩).lower)
        (by norm_num [cell13060]) (by norm_num [cell13060])
      exact ⟨E.1,E.2.trans (by norm_num [cell13060])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy38 (n := 13060) (by norm_num)
        (q := 1 - (cell13060 ⟨38,by decide⟩).lower)
        (by norm_num [cell13060]) (by norm_num [cell13060])
      exact ⟨E.1,E.2.trans (by norm_num [cell13060])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy39 (n := 13060) (by norm_num)
        (q := 1 - (cell13060 ⟨39,by decide⟩).lower)
        (by norm_num [cell13060]) (by norm_num [cell13060])
      exact ⟨E.1,E.2.trans (by norm_num [cell13060])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy40 (n := 13060) (by norm_num)
        (q := 1 - (cell13060 ⟨40,by decide⟩).lower)
        (by norm_num [cell13060]) (by norm_num [cell13060])
      exact ⟨E.1,E.2.trans (by norm_num [cell13060])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy41 (n := 13060) (by norm_num)
        (q := 1 - (cell13060 ⟨41,by decide⟩).lower)
        (by norm_num [cell13060]) (by norm_num [cell13060])
      exact ⟨E.1,E.2.trans (by norm_num [cell13060])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy42 (n := 13060) (by norm_num)
        (q := 1 - (cell13060 ⟨42,by decide⟩).lower)
        (by norm_num [cell13060]) (by norm_num [cell13060])
      exact ⟨E.1,E.2.trans (by norm_num [cell13060])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy43 (n := 13060) (by norm_num)
        (q := 1 - (cell13060 ⟨43,by decide⟩).lower)
        (by norm_num [cell13060]) (by norm_num [cell13060])
      exact ⟨E.1,E.2.trans (by norm_num [cell13060])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy44 (n := 13060) (by norm_num)
        (q := 1 - (cell13060 ⟨44,by decide⟩).lower)
        (by norm_num [cell13060]) (by norm_num [cell13060])
      exact ⟨E.1,E.2.trans (by norm_num [cell13060])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy45 (n := 13060) (by norm_num)
        (q := 1 - (cell13060 ⟨45,by decide⟩).lower)
        (by norm_num [cell13060]) (by norm_num [cell13060])
      exact ⟨E.1,E.2.trans (by norm_num [cell13060])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy46 (n := 13060) (by norm_num)
        (q := 1 - (cell13060 ⟨46,by decide⟩).lower)
        (by norm_num [cell13060]) (by norm_num [cell13060])
      exact ⟨E.1,E.2.trans (by norm_num [cell13060])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy47 (n := 13060) (by norm_num)
        (q := 1 - (cell13060 ⟨47,by decide⟩).lower)
        (by norm_num [cell13060]) (by norm_num [cell13060])
      exact ⟨E.1,E.2.trans (by norm_num [cell13060])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy48 (n := 13060) (by norm_num)
        (q := 1 - (cell13060 ⟨48,by decide⟩).lower)
        (by norm_num [cell13060]) (by norm_num [cell13060])
      exact ⟨E.1,E.2.trans (by norm_num [cell13060])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy49 (n := 13060) (by norm_num)
        (q := 1 - (cell13060 ⟨49,by decide⟩).lower)
        (by norm_num [cell13060]) (by norm_num [cell13060])
      exact ⟨E.1,E.2.trans (by norm_num [cell13060])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy50 (n := 13060) (by norm_num)
        (q := 1 - (cell13060 ⟨50,by decide⟩).lower)
        (by norm_num [cell13060]) (by norm_num [cell13060])
      exact ⟨E.1,E.2.trans (by norm_num [cell13060])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy51 (n := 13060) (by norm_num)
        (q := 1 - (cell13060 ⟨51,by decide⟩).lower)
        (by norm_num [cell13060]) (by norm_num [cell13060])
      exact ⟨E.1,E.2.trans (by norm_num [cell13060])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy52 (n := 13060) (by norm_num)
        (q := 1 - (cell13060 ⟨52,by decide⟩).lower)
        (by norm_num [cell13060]) (by norm_num [cell13060])
      exact ⟨E.1,E.2.trans (by norm_num [cell13060])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13060

/-! Source-cell containment and simple scalar guards at 13060. -/
namespace BstLean.Part269.N13060
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13060)
open BstLean.Part268 (cell13060)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13060 ⟨10,by decide⟩).lower ∧ (cell13060 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13060 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13060 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13060 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13060 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13060 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13060,cell13060,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13060 ⟨11,by decide⟩).lower ∧ (cell13060 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13060 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13060 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13060 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13060 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13060 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13060,cell13060,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13060 ⟨12,by decide⟩).lower ∧ (cell13060 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13060 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13060 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13060 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13060 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13060 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13060,cell13060,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13060 ⟨13,by decide⟩).lower ∧ (cell13060 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13060 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13060 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13060 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13060 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13060 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13060,cell13060,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13060 ⟨14,by decide⟩).lower ∧ (cell13060 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13060 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13060 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13060 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13060 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13060 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13060,cell13060,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13060 ⟨15,by decide⟩).lower ∧ (cell13060 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13060 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13060 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13060 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13060 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13060 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13060,cell13060,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13060 ⟨16,by decide⟩).lower ∧ (cell13060 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13060 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13060 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13060 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13060 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13060 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13060,cell13060,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13060 ⟨17,by decide⟩).lower ∧ (cell13060 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13060 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13060 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13060 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13060 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13060 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13060,cell13060,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13060 ⟨18,by decide⟩).lower ∧ (cell13060 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13060 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13060 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13060 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13060 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13060 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13060,cell13060,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13060 ⟨19,by decide⟩).lower ∧ (cell13060 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13060 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13060 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13060 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13060 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13060 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13060,cell13060,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13060 ⟨20,by decide⟩).lower ∧ (cell13060 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13060 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13060 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13060 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13060 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13060 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13060,cell13060,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13060 ⟨21,by decide⟩).lower ∧ (cell13060 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13060 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13060 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13060 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13060 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13060 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13060,cell13060,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13060 ⟨22,by decide⟩).lower ∧ (cell13060 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13060 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13060 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13060 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13060 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13060 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13060,cell13060,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13060 ⟨23,by decide⟩).lower ∧ (cell13060 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13060 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13060 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13060 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13060 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13060 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13060,cell13060,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13060 ⟨24,by decide⟩).lower ∧ (cell13060 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13060 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13060 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13060 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13060 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13060 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13060,cell13060,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13060 ⟨25,by decide⟩).lower ∧ (cell13060 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13060 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13060 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13060 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13060 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13060 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13060,cell13060,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13060 ⟨26,by decide⟩).lower ∧ (cell13060 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13060 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13060 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13060 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13060 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13060 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13060,cell13060,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13060 ⟨27,by decide⟩).lower ∧ (cell13060 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13060 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13060 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13060 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13060 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13060 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13060,cell13060,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13060 ⟨28,by decide⟩).lower ∧ (cell13060 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13060 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13060 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13060 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13060 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13060 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13060,cell13060,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13060 ⟨29,by decide⟩).lower ∧ (cell13060 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13060 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13060 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13060 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13060 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13060 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13060,cell13060,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13060 ⟨30,by decide⟩).lower ∧ (cell13060 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13060 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13060 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13060 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13060 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13060 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13060,cell13060,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13060 ⟨31,by decide⟩).lower ∧ (cell13060 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13060 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13060 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13060 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13060 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13060 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13060,cell13060,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13060 ⟨32,by decide⟩).lower ∧ (cell13060 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13060 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13060 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13060 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13060 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13060 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13060,cell13060,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13060 ⟨33,by decide⟩).lower ∧ (cell13060 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13060 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13060 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13060 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13060 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13060 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13060,cell13060,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13060 ⟨34,by decide⟩).lower ∧ (cell13060 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13060 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13060 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13060 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13060 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13060 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13060,cell13060,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13060 ⟨35,by decide⟩).lower ∧ (cell13060 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13060 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13060 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13060 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13060 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13060 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13060,cell13060,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13060 ⟨36,by decide⟩).lower ∧ (cell13060 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13060 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13060 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13060 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13060 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13060 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13060,cell13060,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13060 ⟨37,by decide⟩).lower ∧ (cell13060 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13060 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13060 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13060 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13060 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13060 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13060,cell13060,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13060 ⟨38,by decide⟩).lower ∧ (cell13060 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13060 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13060 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13060 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13060 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13060 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13060,cell13060,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13060 ⟨39,by decide⟩).lower ∧ (cell13060 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13060 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13060 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13060 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13060 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13060 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13060,cell13060,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13060 ⟨40,by decide⟩).lower ∧ (cell13060 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13060 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13060 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13060 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13060 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13060 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13060,cell13060,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13060 ⟨41,by decide⟩).lower ∧ (cell13060 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13060 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13060 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13060 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13060 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13060 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13060,cell13060,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13060 ⟨42,by decide⟩).lower ∧ (cell13060 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13060 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13060 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13060 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13060 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13060 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13060,cell13060,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13060 ⟨43,by decide⟩).lower ∧ (cell13060 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13060 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13060 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13060 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13060 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13060 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13060,cell13060,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13060 ⟨44,by decide⟩).lower ∧ (cell13060 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13060 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13060 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13060 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13060 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13060 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13060,cell13060,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13060 ⟨45,by decide⟩).lower ∧ (cell13060 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13060 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13060 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13060 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13060 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13060 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13060,cell13060,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13060 ⟨46,by decide⟩).lower ∧ (cell13060 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13060 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13060 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13060 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13060 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13060 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13060,cell13060,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13060 ⟨47,by decide⟩).lower ∧ (cell13060 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13060 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13060 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13060 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13060 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13060 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13060,cell13060,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13060 ⟨48,by decide⟩).lower ∧ (cell13060 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13060 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13060 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13060 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13060 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13060 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13060,cell13060,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13060 ⟨49,by decide⟩).lower ∧ (cell13060 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13060 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13060 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13060 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13060 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13060 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13060,cell13060,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13060 ⟨50,by decide⟩).lower ∧ (cell13060 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13060 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13060 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13060 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13060 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13060 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13060,cell13060,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13060 ⟨51,by decide⟩).lower ∧ (cell13060 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13060 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13060 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13060 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13060 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13060 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13060,cell13060,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13060 ⟨52,by decide⟩).lower ∧ (cell13060 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13060 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13060 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13060 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13060 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13060 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13060,cell13060,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13060 i).lower ∧
    (cell13060 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13060 i).upper ≤ (0.532 : ℝ) ∧
    (cell13060 i).centre ≤ (0.1 : ℝ) ∧ (cell13060 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13060 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13060 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13060

/-! The local source numeric instances at 13060 have no network premises. -/
namespace BstLean.Part269.N13060
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13060)
open BstLean.Part268 (cell13060)

noncomputable def sourceNumerics13060 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13060 (cell13060 i)
      scalarRow13060.M scalarRow13060.H scalarRow13060.xi := by
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
    energy_allowance := scalarRow13060.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13060]
    centre_nonneg := (scalarRow13060.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D28.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13060])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13060
/-! Actual 13061 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13061
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13061 ≤ (1.035306556049 : ℝ) := by
  have hr : (114.284732138636 : ℝ) ≤ √(13061 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.284732138636 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13061 13061 (11 / 1000) ≤
    (0.008364082495 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13061) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.284732138636 : ℝ) ≤ √(13061 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13061)
  have hdiv : K / √(13061 : ℝ) ≤ K / 114.284732138636 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.284732138636 ≤ (0.008364082495 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13061.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13061 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13061 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13061 := gPlus_lower 13061
end BstLean.Part269.N13061

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13061
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035306556048 : ℝ) ≤ wn 13061 := by
  have hn : √(13061 : ℝ) ≤ 114.284732138637 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13061 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.284732138637 ≤ 2 / √(13061 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000244800142 : ℝ) ≤ rhoBar 13061 BstLean.Part154.csC ∧
    rhoBar 13061 BstLean.Part154.csC ≤ 0.000244800521 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035306556048 : ℝ) / (1.295212 * 13061) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035306556049 : ℝ) / (1.29521 * 13061) := by gcongr
      _ ≤ (0.000244800521 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13061 BstLean.Part154.csC) ≤ 0.000979262012 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13061 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13061 BstLean.Part154.csC) (piBar (rhoBar 13061 BstLean.Part154.csC)) ≤ 0.000186980045 ∧
    cc1 (rhoBar 13061 BstLean.Part154.csC) (piBar (rhoBar 13061 BstLean.Part154.csC)) ≤ 0.000118976694 ∧
    cc2 (rhoBar 13061 BstLean.Part154.csC) ≤ 0.000069066944 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13061 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13061 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13061 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13061 BstLean.Part154.csC * nuR (rhoBar 13061 BstLean.Part154.csC)) ≤ 0.000489616024 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000244800521 : ℝ) * 0.000979262012 := by gcongr
      _ ≤ (0.000489616024 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13061 BstLean.Part154.csC) * nuR (rhoBar 13061 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000979262012 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13061 BstLean.Part154.csC) * rhoBar 13061 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000244800521 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000244800521 / 2 + 0.399 * 0.000979262012 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000186980045 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000489616024 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118976694 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000244800521 / 1.414213562 := by gcongr
      _ ≤ (0.000069066944 : ℝ) := by norm_num

end BstLean.Part269.N13061

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13061
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13061 BstLean.Part154.csC) (piBar (rhoBar 13061 BstLean.Part154.csC)) ≤ 1.50982E-7 := by
  have hr0 : 0 ≤ rhoBar 13061 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13061 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13061 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13061 BstLean.Part154.csC) (piBar (rhoBar 13061 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13061 BstLean.Part154.csC) (piBar (rhoBar 13061 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13061 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000186980045 : ℝ) ^ 2 + 0.000118976694 ^ 2 + 3 * 0.000069066944 ^ 2 +
        2 * 0.797885 * 0.000186980045 * 0.000118976694 + 2 * 0.000186980045 * 0.000069066944 +
        4 * 0.797885 * 0.000118976694 * 0.000069066944 := by gcongr
    _ ≤ (1.50982E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13061 BstLean.Part154.csC Θ ≤ 0.002554126860 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13061 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13061 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13061 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13061 BstLean.Part154.csC) (piBar (rhoBar 13061 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13061 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035306556049 * 1.50982E-7 / (0.000244800142 : ℝ) := by gcongr
    _ ≤ 0.002554126860 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13061 BstLean.Part154.csC Θ ≤ 0.002832571276 + 0.000645388923 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13061 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13061 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13061 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035306556049 : ℝ) * ((2 * Θ * 0.000244800521 +
        (6863 / 10000) * 0.000244800521 * 13061 * 0.000979262012) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002832571276 + 0.000645388923 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13061 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13061 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13061 0.011 Θ ∧ gammaRatio 13061 0.011 Θ ≤ 0.000084156089 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13061 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035306556049 : ℝ) * 0.525 / ((1 - 0.011) * 13061) := by gcongr
      _ ≤ (0.000084156089 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13061 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13061 0.011 Θ) :=
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
    badAllowance 13061 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000383749387 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13061 BstLean.Part154.csC) 1.22 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 2 (rhoBar 13061 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13061 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13061 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13061 0.011 Θ) 1.12 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 1 (gammaRatio 13061 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13061 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13061 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13061 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13061 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035306556049 : ℝ) * 13061 *
        (1.3781E-8 / 1.1045361 + 1.5230E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000383749387 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13061 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003216320663 + 0.003199515783 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13061

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13061
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13061 BstLean.Part154.csC) (piBar (rhoBar 13061 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13061 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13061 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13061 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13061 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13061 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13061 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13061 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13061 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13061 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13061 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13061 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13061 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13061 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13061 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051746099479 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13061) ≤ 0.010449668637 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13061 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035306556049)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010449668637 + 2 * 0.737676 / 13061) := by gcongr
    _ ≤ (0.051746099479 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13061 12 ≤ 0.0015 := by
  exact BstLean.Part269.S28.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13061

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13061
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560519442554 : ℝ) ≤ plow 13061 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13061) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052402666450)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001340916602) : eMP 13061 0.011 xi bn ≤ 0.001154885093 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13061 : ℝ) * (1 - 0.011))) ≤ 0.000571070182 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001340916602 / (13061 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000571070182 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000571070182 : ℝ) + 3.141593 * 0.052402666450 / (13061 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001154885093 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052402666450)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001340916602) : PiBarMP 13061 12 0.011 xi bn ≤ 0.158984882531 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13061 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036618528125 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.654427982371 : ℝ) ≤ √((13061 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.284732138636 : ℝ) ≤ √(13061 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13061) ≤ 0.121909619965 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036618528125 + 0.052402666450 * 1.772454 / (2 * (113.654427982371 : ℝ))) * (1 + 0.001154885093) +
        8 / (13061 * 114.284732138636) + 0.121909619965 := by gcongr
    _ ≤ (0.158984882531 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052402666450)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001340916602) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280662386471) :
    parallelOracle 13061 0.011 xi bn cd ≤ 0.159948000980 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13061 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13061 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560519442554 : ℝ) ≤ plow 13061 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.284732138636 : ℝ) ≤ √(13061 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280662386471 : ℝ) / (2 * 0.560519442554 * 114.284732138636)) * 0.158984882531 +
        0.280662386471 ^ 2 / (2 * 0.560519442554 * 114.284732138636) := by gcongr
    _ ≤ (0.159948000980 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052402666450) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001340916602)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280662386471) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13061 13061 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560519442554 : ℝ) ≤ plow 13061 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.284732138636 : ℝ) ≤ √(13061 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13061 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13061 Θ 1.22 ≤ 0.011603479093 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.284732138636 := by gcongr <;> linarith
      _ ≤ (0.011603479093 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13061 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13061 13061 0.011 ≤ 0.008364082495 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13061 13061 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13061 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13061 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13061 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13061 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159948000980 + 0.011603479093 + (0.008364082495 : ℝ) *
        (1 + 2 * (0.280662386471 + 0.011603479093) / (0.560519442554 * 114.284732138636))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13061]

end BstLean.Part269.N13061

/-! The original eight local profiles supply actual 13061 moment certificates. -/
namespace BstLean.Part269.N13061
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13061 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13061 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13061 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052402666450 ∧
    0 ≤ bN 13061 BstLean.Part154.csC (groupTheta g) ∧ bN 13061 BstLean.Part154.csC (groupTheta g) ≤ 0.001340916602 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13061 13061 0.011
      (momentAllowance 13061 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13061 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13061 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13061 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13061 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13061 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228916286992 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13061 0.011
      (momentAllowance 13061 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13061 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13061
/-! The actual computed-centre upper energy formula at 13061. -/
namespace BstLean.Part269.N13061
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13061

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13061
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13061)
open BstLean.Part268 (cell13061)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084501854125
  | 2 => 0.085428470905
  | 3 => 0.086350988342
  | 4 => 0.087270298274
  | 5 => 0.088187494676
  | 6 => 0.089103905566
  | 7 => 0.090021128262
  | 8 => 0.090941068112
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13061 13061 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13061 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003218831707 + 0.003202305177 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S28.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13061

/-! Actual upper energy certificates on all 43 source endpoints at 13061. -/
namespace BstLean.Part269.N13061
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13061)
open BstLean.Part268 (cell13061)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13061 (gMinus 13061) (1 - (cell13061 i).lower) ≤ 1 ∧
    energyUpper 13061 (gMinus 13061) (BstLean.Part211.gPlus 13061)
      (finiteEnergy 13061 13061 0.011) (1 - (cell13061 i).lower) ≤
      (cell13061 i).energy := by
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
      have E := BstLean.Part269.S28.uniformEnergy10 (n := 13061) (by norm_num)
        (q := 1 - (cell13061 ⟨10,by decide⟩).lower)
        (by norm_num [cell13061]) (by norm_num [cell13061])
      exact ⟨E.1,E.2.trans (by norm_num [cell13061])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy11 (n := 13061) (by norm_num)
        (q := 1 - (cell13061 ⟨11,by decide⟩).lower)
        (by norm_num [cell13061]) (by norm_num [cell13061])
      exact ⟨E.1,E.2.trans (by norm_num [cell13061])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy12 (n := 13061) (by norm_num)
        (q := 1 - (cell13061 ⟨12,by decide⟩).lower)
        (by norm_num [cell13061]) (by norm_num [cell13061])
      exact ⟨E.1,E.2.trans (by norm_num [cell13061])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy13 (n := 13061) (by norm_num)
        (q := 1 - (cell13061 ⟨13,by decide⟩).lower)
        (by norm_num [cell13061]) (by norm_num [cell13061])
      exact ⟨E.1,E.2.trans (by norm_num [cell13061])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy14 (n := 13061) (by norm_num)
        (q := 1 - (cell13061 ⟨14,by decide⟩).lower)
        (by norm_num [cell13061]) (by norm_num [cell13061])
      exact ⟨E.1,E.2.trans (by norm_num [cell13061])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy15 (n := 13061) (by norm_num)
        (q := 1 - (cell13061 ⟨15,by decide⟩).lower)
        (by norm_num [cell13061]) (by norm_num [cell13061])
      exact ⟨E.1,E.2.trans (by norm_num [cell13061])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy16 (n := 13061) (by norm_num)
        (q := 1 - (cell13061 ⟨16,by decide⟩).lower)
        (by norm_num [cell13061]) (by norm_num [cell13061])
      exact ⟨E.1,E.2.trans (by norm_num [cell13061])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy17 (n := 13061) (by norm_num)
        (q := 1 - (cell13061 ⟨17,by decide⟩).lower)
        (by norm_num [cell13061]) (by norm_num [cell13061])
      exact ⟨E.1,E.2.trans (by norm_num [cell13061])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy18 (n := 13061) (by norm_num)
        (q := 1 - (cell13061 ⟨18,by decide⟩).lower)
        (by norm_num [cell13061]) (by norm_num [cell13061])
      exact ⟨E.1,E.2.trans (by norm_num [cell13061])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy19 (n := 13061) (by norm_num)
        (q := 1 - (cell13061 ⟨19,by decide⟩).lower)
        (by norm_num [cell13061]) (by norm_num [cell13061])
      exact ⟨E.1,E.2.trans (by norm_num [cell13061])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy20 (n := 13061) (by norm_num)
        (q := 1 - (cell13061 ⟨20,by decide⟩).lower)
        (by norm_num [cell13061]) (by norm_num [cell13061])
      exact ⟨E.1,E.2.trans (by norm_num [cell13061])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy21 (n := 13061) (by norm_num)
        (q := 1 - (cell13061 ⟨21,by decide⟩).lower)
        (by norm_num [cell13061]) (by norm_num [cell13061])
      exact ⟨E.1,E.2.trans (by norm_num [cell13061])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy22 (n := 13061) (by norm_num)
        (q := 1 - (cell13061 ⟨22,by decide⟩).lower)
        (by norm_num [cell13061]) (by norm_num [cell13061])
      exact ⟨E.1,E.2.trans (by norm_num [cell13061])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy23 (n := 13061) (by norm_num)
        (q := 1 - (cell13061 ⟨23,by decide⟩).lower)
        (by norm_num [cell13061]) (by norm_num [cell13061])
      exact ⟨E.1,E.2.trans (by norm_num [cell13061])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy24 (n := 13061) (by norm_num)
        (q := 1 - (cell13061 ⟨24,by decide⟩).lower)
        (by norm_num [cell13061]) (by norm_num [cell13061])
      exact ⟨E.1,E.2.trans (by norm_num [cell13061])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy25 (n := 13061) (by norm_num)
        (q := 1 - (cell13061 ⟨25,by decide⟩).lower)
        (by norm_num [cell13061]) (by norm_num [cell13061])
      exact ⟨E.1,E.2.trans (by norm_num [cell13061])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy26 (n := 13061) (by norm_num)
        (q := 1 - (cell13061 ⟨26,by decide⟩).lower)
        (by norm_num [cell13061]) (by norm_num [cell13061])
      exact ⟨E.1,E.2.trans (by norm_num [cell13061])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy27 (n := 13061) (by norm_num)
        (q := 1 - (cell13061 ⟨27,by decide⟩).lower)
        (by norm_num [cell13061]) (by norm_num [cell13061])
      exact ⟨E.1,E.2.trans (by norm_num [cell13061])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy28 (n := 13061) (by norm_num)
        (q := 1 - (cell13061 ⟨28,by decide⟩).lower)
        (by norm_num [cell13061]) (by norm_num [cell13061])
      exact ⟨E.1,E.2.trans (by norm_num [cell13061])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy29 (n := 13061) (by norm_num)
        (q := 1 - (cell13061 ⟨29,by decide⟩).lower)
        (by norm_num [cell13061]) (by norm_num [cell13061])
      exact ⟨E.1,E.2.trans (by norm_num [cell13061])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy30 (n := 13061) (by norm_num)
        (q := 1 - (cell13061 ⟨30,by decide⟩).lower)
        (by norm_num [cell13061]) (by norm_num [cell13061])
      exact ⟨E.1,E.2.trans (by norm_num [cell13061])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy31 (n := 13061) (by norm_num)
        (q := 1 - (cell13061 ⟨31,by decide⟩).lower)
        (by norm_num [cell13061]) (by norm_num [cell13061])
      exact ⟨E.1,E.2.trans (by norm_num [cell13061])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy32 (n := 13061) (by norm_num)
        (q := 1 - (cell13061 ⟨32,by decide⟩).lower)
        (by norm_num [cell13061]) (by norm_num [cell13061])
      exact ⟨E.1,E.2.trans (by norm_num [cell13061])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy33 (n := 13061) (by norm_num)
        (q := 1 - (cell13061 ⟨33,by decide⟩).lower)
        (by norm_num [cell13061]) (by norm_num [cell13061])
      exact ⟨E.1,E.2.trans (by norm_num [cell13061])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy34 (n := 13061) (by norm_num)
        (q := 1 - (cell13061 ⟨34,by decide⟩).lower)
        (by norm_num [cell13061]) (by norm_num [cell13061])
      exact ⟨E.1,E.2.trans (by norm_num [cell13061])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy35 (n := 13061) (by norm_num)
        (q := 1 - (cell13061 ⟨35,by decide⟩).lower)
        (by norm_num [cell13061]) (by norm_num [cell13061])
      exact ⟨E.1,E.2.trans (by norm_num [cell13061])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy36 (n := 13061) (by norm_num)
        (q := 1 - (cell13061 ⟨36,by decide⟩).lower)
        (by norm_num [cell13061]) (by norm_num [cell13061])
      exact ⟨E.1,E.2.trans (by norm_num [cell13061])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy37 (n := 13061) (by norm_num)
        (q := 1 - (cell13061 ⟨37,by decide⟩).lower)
        (by norm_num [cell13061]) (by norm_num [cell13061])
      exact ⟨E.1,E.2.trans (by norm_num [cell13061])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy38 (n := 13061) (by norm_num)
        (q := 1 - (cell13061 ⟨38,by decide⟩).lower)
        (by norm_num [cell13061]) (by norm_num [cell13061])
      exact ⟨E.1,E.2.trans (by norm_num [cell13061])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy39 (n := 13061) (by norm_num)
        (q := 1 - (cell13061 ⟨39,by decide⟩).lower)
        (by norm_num [cell13061]) (by norm_num [cell13061])
      exact ⟨E.1,E.2.trans (by norm_num [cell13061])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy40 (n := 13061) (by norm_num)
        (q := 1 - (cell13061 ⟨40,by decide⟩).lower)
        (by norm_num [cell13061]) (by norm_num [cell13061])
      exact ⟨E.1,E.2.trans (by norm_num [cell13061])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy41 (n := 13061) (by norm_num)
        (q := 1 - (cell13061 ⟨41,by decide⟩).lower)
        (by norm_num [cell13061]) (by norm_num [cell13061])
      exact ⟨E.1,E.2.trans (by norm_num [cell13061])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy42 (n := 13061) (by norm_num)
        (q := 1 - (cell13061 ⟨42,by decide⟩).lower)
        (by norm_num [cell13061]) (by norm_num [cell13061])
      exact ⟨E.1,E.2.trans (by norm_num [cell13061])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy43 (n := 13061) (by norm_num)
        (q := 1 - (cell13061 ⟨43,by decide⟩).lower)
        (by norm_num [cell13061]) (by norm_num [cell13061])
      exact ⟨E.1,E.2.trans (by norm_num [cell13061])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy44 (n := 13061) (by norm_num)
        (q := 1 - (cell13061 ⟨44,by decide⟩).lower)
        (by norm_num [cell13061]) (by norm_num [cell13061])
      exact ⟨E.1,E.2.trans (by norm_num [cell13061])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy45 (n := 13061) (by norm_num)
        (q := 1 - (cell13061 ⟨45,by decide⟩).lower)
        (by norm_num [cell13061]) (by norm_num [cell13061])
      exact ⟨E.1,E.2.trans (by norm_num [cell13061])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy46 (n := 13061) (by norm_num)
        (q := 1 - (cell13061 ⟨46,by decide⟩).lower)
        (by norm_num [cell13061]) (by norm_num [cell13061])
      exact ⟨E.1,E.2.trans (by norm_num [cell13061])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy47 (n := 13061) (by norm_num)
        (q := 1 - (cell13061 ⟨47,by decide⟩).lower)
        (by norm_num [cell13061]) (by norm_num [cell13061])
      exact ⟨E.1,E.2.trans (by norm_num [cell13061])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy48 (n := 13061) (by norm_num)
        (q := 1 - (cell13061 ⟨48,by decide⟩).lower)
        (by norm_num [cell13061]) (by norm_num [cell13061])
      exact ⟨E.1,E.2.trans (by norm_num [cell13061])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy49 (n := 13061) (by norm_num)
        (q := 1 - (cell13061 ⟨49,by decide⟩).lower)
        (by norm_num [cell13061]) (by norm_num [cell13061])
      exact ⟨E.1,E.2.trans (by norm_num [cell13061])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy50 (n := 13061) (by norm_num)
        (q := 1 - (cell13061 ⟨50,by decide⟩).lower)
        (by norm_num [cell13061]) (by norm_num [cell13061])
      exact ⟨E.1,E.2.trans (by norm_num [cell13061])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy51 (n := 13061) (by norm_num)
        (q := 1 - (cell13061 ⟨51,by decide⟩).lower)
        (by norm_num [cell13061]) (by norm_num [cell13061])
      exact ⟨E.1,E.2.trans (by norm_num [cell13061])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy52 (n := 13061) (by norm_num)
        (q := 1 - (cell13061 ⟨52,by decide⟩).lower)
        (by norm_num [cell13061]) (by norm_num [cell13061])
      exact ⟨E.1,E.2.trans (by norm_num [cell13061])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13061

/-! Source-cell containment and simple scalar guards at 13061. -/
namespace BstLean.Part269.N13061
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13061)
open BstLean.Part268 (cell13061)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13061 ⟨10,by decide⟩).lower ∧ (cell13061 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13061 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13061 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13061 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13061 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13061 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13061,cell13061,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13061 ⟨11,by decide⟩).lower ∧ (cell13061 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13061 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13061 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13061 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13061 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13061 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13061,cell13061,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13061 ⟨12,by decide⟩).lower ∧ (cell13061 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13061 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13061 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13061 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13061 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13061 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13061,cell13061,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13061 ⟨13,by decide⟩).lower ∧ (cell13061 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13061 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13061 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13061 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13061 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13061 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13061,cell13061,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13061 ⟨14,by decide⟩).lower ∧ (cell13061 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13061 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13061 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13061 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13061 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13061 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13061,cell13061,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13061 ⟨15,by decide⟩).lower ∧ (cell13061 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13061 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13061 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13061 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13061 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13061 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13061,cell13061,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13061 ⟨16,by decide⟩).lower ∧ (cell13061 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13061 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13061 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13061 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13061 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13061 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13061,cell13061,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13061 ⟨17,by decide⟩).lower ∧ (cell13061 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13061 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13061 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13061 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13061 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13061 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13061,cell13061,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13061 ⟨18,by decide⟩).lower ∧ (cell13061 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13061 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13061 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13061 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13061 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13061 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13061,cell13061,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13061 ⟨19,by decide⟩).lower ∧ (cell13061 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13061 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13061 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13061 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13061 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13061 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13061,cell13061,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13061 ⟨20,by decide⟩).lower ∧ (cell13061 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13061 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13061 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13061 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13061 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13061 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13061,cell13061,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13061 ⟨21,by decide⟩).lower ∧ (cell13061 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13061 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13061 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13061 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13061 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13061 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13061,cell13061,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13061 ⟨22,by decide⟩).lower ∧ (cell13061 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13061 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13061 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13061 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13061 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13061 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13061,cell13061,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13061 ⟨23,by decide⟩).lower ∧ (cell13061 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13061 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13061 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13061 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13061 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13061 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13061,cell13061,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13061 ⟨24,by decide⟩).lower ∧ (cell13061 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13061 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13061 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13061 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13061 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13061 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13061,cell13061,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13061 ⟨25,by decide⟩).lower ∧ (cell13061 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13061 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13061 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13061 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13061 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13061 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13061,cell13061,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13061 ⟨26,by decide⟩).lower ∧ (cell13061 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13061 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13061 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13061 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13061 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13061 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13061,cell13061,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13061 ⟨27,by decide⟩).lower ∧ (cell13061 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13061 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13061 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13061 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13061 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13061 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13061,cell13061,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13061 ⟨28,by decide⟩).lower ∧ (cell13061 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13061 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13061 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13061 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13061 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13061 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13061,cell13061,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13061 ⟨29,by decide⟩).lower ∧ (cell13061 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13061 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13061 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13061 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13061 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13061 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13061,cell13061,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13061 ⟨30,by decide⟩).lower ∧ (cell13061 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13061 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13061 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13061 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13061 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13061 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13061,cell13061,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13061 ⟨31,by decide⟩).lower ∧ (cell13061 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13061 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13061 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13061 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13061 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13061 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13061,cell13061,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13061 ⟨32,by decide⟩).lower ∧ (cell13061 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13061 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13061 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13061 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13061 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13061 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13061,cell13061,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13061 ⟨33,by decide⟩).lower ∧ (cell13061 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13061 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13061 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13061 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13061 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13061 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13061,cell13061,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13061 ⟨34,by decide⟩).lower ∧ (cell13061 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13061 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13061 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13061 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13061 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13061 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13061,cell13061,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13061 ⟨35,by decide⟩).lower ∧ (cell13061 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13061 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13061 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13061 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13061 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13061 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13061,cell13061,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13061 ⟨36,by decide⟩).lower ∧ (cell13061 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13061 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13061 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13061 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13061 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13061 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13061,cell13061,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13061 ⟨37,by decide⟩).lower ∧ (cell13061 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13061 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13061 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13061 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13061 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13061 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13061,cell13061,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13061 ⟨38,by decide⟩).lower ∧ (cell13061 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13061 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13061 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13061 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13061 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13061 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13061,cell13061,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13061 ⟨39,by decide⟩).lower ∧ (cell13061 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13061 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13061 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13061 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13061 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13061 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13061,cell13061,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13061 ⟨40,by decide⟩).lower ∧ (cell13061 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13061 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13061 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13061 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13061 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13061 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13061,cell13061,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13061 ⟨41,by decide⟩).lower ∧ (cell13061 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13061 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13061 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13061 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13061 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13061 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13061,cell13061,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13061 ⟨42,by decide⟩).lower ∧ (cell13061 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13061 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13061 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13061 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13061 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13061 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13061,cell13061,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13061 ⟨43,by decide⟩).lower ∧ (cell13061 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13061 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13061 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13061 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13061 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13061 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13061,cell13061,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13061 ⟨44,by decide⟩).lower ∧ (cell13061 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13061 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13061 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13061 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13061 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13061 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13061,cell13061,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13061 ⟨45,by decide⟩).lower ∧ (cell13061 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13061 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13061 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13061 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13061 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13061 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13061,cell13061,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13061 ⟨46,by decide⟩).lower ∧ (cell13061 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13061 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13061 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13061 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13061 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13061 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13061,cell13061,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13061 ⟨47,by decide⟩).lower ∧ (cell13061 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13061 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13061 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13061 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13061 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13061 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13061,cell13061,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13061 ⟨48,by decide⟩).lower ∧ (cell13061 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13061 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13061 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13061 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13061 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13061 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13061,cell13061,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13061 ⟨49,by decide⟩).lower ∧ (cell13061 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13061 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13061 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13061 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13061 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13061 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13061,cell13061,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13061 ⟨50,by decide⟩).lower ∧ (cell13061 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13061 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13061 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13061 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13061 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13061 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13061,cell13061,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13061 ⟨51,by decide⟩).lower ∧ (cell13061 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13061 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13061 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13061 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13061 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13061 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13061,cell13061,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13061 ⟨52,by decide⟩).lower ∧ (cell13061 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13061 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13061 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13061 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13061 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13061 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13061,cell13061,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13061 i).lower ∧
    (cell13061 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13061 i).upper ≤ (0.532 : ℝ) ∧
    (cell13061 i).centre ≤ (0.1 : ℝ) ∧ (cell13061 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13061 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13061 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13061

/-! The local source numeric instances at 13061 have no network premises. -/
namespace BstLean.Part269.N13061
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13061)
open BstLean.Part268 (cell13061)

noncomputable def sourceNumerics13061 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13061 (cell13061 i)
      scalarRow13061.M scalarRow13061.H scalarRow13061.xi := by
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
    energy_allowance := scalarRow13061.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13061]
    centre_nonneg := (scalarRow13061.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D28.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13061])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13061
/-! Actual 13062 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13062
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13062 ≤ (1.035305192802 : ℝ) := by
  have hr : (114.289107092495 : ℝ) ≤ √(13062 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.289107092495 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13062 13062 (11 / 1000) ≤
    (0.008363762318 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13062) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.289107092495 : ℝ) ≤ √(13062 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13062)
  have hdiv : K / √(13062 : ℝ) ≤ K / 114.289107092495 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.289107092495 ≤ (0.008363762318 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13062.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13062 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13062 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13062 := gPlus_lower 13062
end BstLean.Part269.N13062

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13062
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035305192801 : ℝ) ≤ wn 13062 := by
  have hn : √(13062 : ℝ) ≤ 114.289107092496 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13062 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.289107092496 ≤ 2 / √(13062 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000244781078 : ℝ) ≤ rhoBar 13062 BstLean.Part154.csC ∧
    rhoBar 13062 BstLean.Part154.csC ≤ 0.000244781457 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035305192801 : ℝ) / (1.295212 * 13062) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035305192802 : ℝ) / (1.29521 * 13062) := by gcongr
      _ ≤ (0.000244781457 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13062 BstLean.Part154.csC) ≤ 0.000979185746 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13062 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13062 BstLean.Part154.csC) (piBar (rhoBar 13062 BstLean.Part154.csC)) ≤ 0.000186965483 ∧
    cc1 (rhoBar 13062 BstLean.Part154.csC) (piBar (rhoBar 13062 BstLean.Part154.csC)) ≤ 0.000118967429 ∧
    cc2 (rhoBar 13062 BstLean.Part154.csC) ≤ 0.000069061565 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13062 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13062 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13062 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13062 BstLean.Part154.csC * nuR (rhoBar 13062 BstLean.Part154.csC)) ≤ 0.000489577894 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000244781457 : ℝ) * 0.000979185746 := by gcongr
      _ ≤ (0.000489577894 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13062 BstLean.Part154.csC) * nuR (rhoBar 13062 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000979185746 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13062 BstLean.Part154.csC) * rhoBar 13062 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000244781457 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000244781457 / 2 + 0.399 * 0.000979185746 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000186965483 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000489577894 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118967429 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000244781457 / 1.414213562 := by gcongr
      _ ≤ (0.000069061565 : ℝ) := by norm_num

end BstLean.Part269.N13062

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13062
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13062 BstLean.Part154.csC) (piBar (rhoBar 13062 BstLean.Part154.csC)) ≤ 1.50959E-7 := by
  have hr0 : 0 ≤ rhoBar 13062 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13062 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13062 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13062 BstLean.Part154.csC) (piBar (rhoBar 13062 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13062 BstLean.Part154.csC) (piBar (rhoBar 13062 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13062 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000186965483 : ℝ) ^ 2 + 0.000118967429 ^ 2 + 3 * 0.000069061565 ^ 2 +
        2 * 0.797885 * 0.000186965483 * 0.000118967429 + 2 * 0.000186965483 * 0.000069061565 +
        4 * 0.797885 * 0.000118967429 * 0.000069061565 := by gcongr
    _ ≤ (1.50959E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13062 BstLean.Part154.csC Θ ≤ 0.002553933301 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13062 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13062 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13062 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13062 BstLean.Part154.csC) (piBar (rhoBar 13062 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13062 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035305192802 * 1.50959E-7 / (0.000244781078 : ℝ) := by gcongr
    _ ≤ 0.002553933301 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13062 BstLean.Part154.csC Θ ≤ 0.002832343210 + 0.000645337813 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13062 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13062 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13062 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035305192802 : ℝ) * ((2 * Θ * 0.000244781457 +
        (6863 / 10000) * 0.000244781457 * 13062 * 0.000979185746) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002832343210 + 0.000645337813 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13062 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13062 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13062 0.011 Θ ∧ gammaRatio 13062 0.011 Θ ≤ 0.000084149535 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13062 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035305192802 : ℝ) * 0.525 / ((1 - 0.011) * 13062) := by gcongr
      _ ≤ (0.000084149535 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13062 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13062 0.011 Θ) :=
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
    badAllowance 13062 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000383749387 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13062 BstLean.Part154.csC) 1.22 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 2 (rhoBar 13062 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13062 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13062 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13062 0.011 Θ) 1.12 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 1 (gammaRatio 13062 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13062 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13062 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13062 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13062 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035305192802 : ℝ) * 13062 *
        (1.3781E-8 / 1.1045361 + 1.5230E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000383749387 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13062 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003216092597 + 0.003199271114 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13062

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13062
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13062 BstLean.Part154.csC) (piBar (rhoBar 13062 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13062 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13062 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13062 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13062 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13062 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13062 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13062 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13062 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13062 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13062 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13062 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13062 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13062 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13062 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051744097472 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13062) ≤ 0.010449268627 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13062 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035305192802)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010449268627 + 2 * 0.737676 / 13062) := by gcongr
    _ ≤ (0.051744097472 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13062 12 ≤ 0.0015 := by
  exact BstLean.Part269.S28.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13062

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13062
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560519485308 : ℝ) ≤ plow 13062 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13062) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052402309932)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001340814984) : eMP 13062 0.011 xi bn ≤ 0.001154797033 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13062 : ℝ) * (1 - 0.011))) ≤ 0.000571026683 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001340814984 / (13062 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000571026683 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000571026683 : ℝ) + 3.141593 * 0.052402309932 / (13062 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001154797033 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052402309932)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001340814984) : PiBarMP 13062 12 0.011 xi bn ≤ 0.158978804396 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13062 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036617140577 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.658778807446 : ℝ) ≤ √((13062 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.289107092495 : ℝ) ≤ √(13062 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13062) ≤ 0.121904953300 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036617140577 + 0.052402309932 * 1.772454 / (2 * (113.658778807446 : ℝ))) * (1 + 0.001154797033) +
        8 / (13062 * 114.289107092495) + 0.121904953300 := by gcongr
    _ ≤ (0.158978804396 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052402309932)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001340814984) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280659605754) :
    parallelOracle 13062 0.011 xi bn cd ≤ 0.159941856955 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13062 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13062 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560519485308 : ℝ) ≤ plow 13062 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.289107092495 : ℝ) ≤ √(13062 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280659605754 : ℝ) / (2 * 0.560519485308 * 114.289107092495)) * 0.158978804396 +
        0.280659605754 ^ 2 / (2 * 0.560519485308 * 114.289107092495) := by gcongr
    _ ≤ (0.159941856955 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052402309932) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001340814984)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280659605754) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13062 13062 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560519485308 : ℝ) ≤ plow 13062 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.289107092495 : ℝ) ≤ √(13062 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13062 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13062 Θ 1.22 ≤ 0.011603034916 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.289107092495 := by gcongr <;> linarith
      _ ≤ (0.011603034916 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13062 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13062 13062 0.011 ≤ 0.008363762318 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13062 13062 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13062 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13062 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13062 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13062 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159941856955 + 0.011603034916 + (0.008363762318 : ℝ) *
        (1 + 2 * (0.280659605754 + 0.011603034916) / (0.560519485308 * 114.289107092495))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13062]

end BstLean.Part269.N13062

/-! The original eight local profiles supply actual 13062 moment certificates. -/
namespace BstLean.Part269.N13062
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13062 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13062 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13062 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052402309932 ∧
    0 ≤ bN 13062 BstLean.Part154.csC (groupTheta g) ∧ bN 13062 BstLean.Part154.csC (groupTheta g) ≤ 0.001340814984 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13062 13062 0.011
      (momentAllowance 13062 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13062 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13062 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13062 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13062 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13062 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228915508282 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13062 0.011
      (momentAllowance 13062 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13062 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13062
/-! The actual computed-centre upper energy formula at 13062. -/
namespace BstLean.Part269.N13062
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13062

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13062
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13062)
open BstLean.Part268 (cell13062)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084499283800
  | 2 => 0.085425867705
  | 3 => 0.086348347415
  | 4 => 0.087267613619
  | 5 => 0.088184758938
  | 6 => 0.089101109790
  | 7 => 0.090018261628
  | 8 => 0.090938117635
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13062 13062 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13062 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003218831707 + 0.003202305177 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S28.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13062

/-! Actual upper energy certificates on all 43 source endpoints at 13062. -/
namespace BstLean.Part269.N13062
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13062)
open BstLean.Part268 (cell13062)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13062 (gMinus 13062) (1 - (cell13062 i).lower) ≤ 1 ∧
    energyUpper 13062 (gMinus 13062) (BstLean.Part211.gPlus 13062)
      (finiteEnergy 13062 13062 0.011) (1 - (cell13062 i).lower) ≤
      (cell13062 i).energy := by
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
      have E := BstLean.Part269.S28.uniformEnergy10 (n := 13062) (by norm_num)
        (q := 1 - (cell13062 ⟨10,by decide⟩).lower)
        (by norm_num [cell13062]) (by norm_num [cell13062])
      exact ⟨E.1,E.2.trans (by norm_num [cell13062])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy11 (n := 13062) (by norm_num)
        (q := 1 - (cell13062 ⟨11,by decide⟩).lower)
        (by norm_num [cell13062]) (by norm_num [cell13062])
      exact ⟨E.1,E.2.trans (by norm_num [cell13062])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy12 (n := 13062) (by norm_num)
        (q := 1 - (cell13062 ⟨12,by decide⟩).lower)
        (by norm_num [cell13062]) (by norm_num [cell13062])
      exact ⟨E.1,E.2.trans (by norm_num [cell13062])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy13 (n := 13062) (by norm_num)
        (q := 1 - (cell13062 ⟨13,by decide⟩).lower)
        (by norm_num [cell13062]) (by norm_num [cell13062])
      exact ⟨E.1,E.2.trans (by norm_num [cell13062])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy14 (n := 13062) (by norm_num)
        (q := 1 - (cell13062 ⟨14,by decide⟩).lower)
        (by norm_num [cell13062]) (by norm_num [cell13062])
      exact ⟨E.1,E.2.trans (by norm_num [cell13062])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy15 (n := 13062) (by norm_num)
        (q := 1 - (cell13062 ⟨15,by decide⟩).lower)
        (by norm_num [cell13062]) (by norm_num [cell13062])
      exact ⟨E.1,E.2.trans (by norm_num [cell13062])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy16 (n := 13062) (by norm_num)
        (q := 1 - (cell13062 ⟨16,by decide⟩).lower)
        (by norm_num [cell13062]) (by norm_num [cell13062])
      exact ⟨E.1,E.2.trans (by norm_num [cell13062])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy17 (n := 13062) (by norm_num)
        (q := 1 - (cell13062 ⟨17,by decide⟩).lower)
        (by norm_num [cell13062]) (by norm_num [cell13062])
      exact ⟨E.1,E.2.trans (by norm_num [cell13062])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy18 (n := 13062) (by norm_num)
        (q := 1 - (cell13062 ⟨18,by decide⟩).lower)
        (by norm_num [cell13062]) (by norm_num [cell13062])
      exact ⟨E.1,E.2.trans (by norm_num [cell13062])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy19 (n := 13062) (by norm_num)
        (q := 1 - (cell13062 ⟨19,by decide⟩).lower)
        (by norm_num [cell13062]) (by norm_num [cell13062])
      exact ⟨E.1,E.2.trans (by norm_num [cell13062])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy20 (n := 13062) (by norm_num)
        (q := 1 - (cell13062 ⟨20,by decide⟩).lower)
        (by norm_num [cell13062]) (by norm_num [cell13062])
      exact ⟨E.1,E.2.trans (by norm_num [cell13062])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy21 (n := 13062) (by norm_num)
        (q := 1 - (cell13062 ⟨21,by decide⟩).lower)
        (by norm_num [cell13062]) (by norm_num [cell13062])
      exact ⟨E.1,E.2.trans (by norm_num [cell13062])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy22 (n := 13062) (by norm_num)
        (q := 1 - (cell13062 ⟨22,by decide⟩).lower)
        (by norm_num [cell13062]) (by norm_num [cell13062])
      exact ⟨E.1,E.2.trans (by norm_num [cell13062])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy23 (n := 13062) (by norm_num)
        (q := 1 - (cell13062 ⟨23,by decide⟩).lower)
        (by norm_num [cell13062]) (by norm_num [cell13062])
      exact ⟨E.1,E.2.trans (by norm_num [cell13062])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy24 (n := 13062) (by norm_num)
        (q := 1 - (cell13062 ⟨24,by decide⟩).lower)
        (by norm_num [cell13062]) (by norm_num [cell13062])
      exact ⟨E.1,E.2.trans (by norm_num [cell13062])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy25 (n := 13062) (by norm_num)
        (q := 1 - (cell13062 ⟨25,by decide⟩).lower)
        (by norm_num [cell13062]) (by norm_num [cell13062])
      exact ⟨E.1,E.2.trans (by norm_num [cell13062])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy26 (n := 13062) (by norm_num)
        (q := 1 - (cell13062 ⟨26,by decide⟩).lower)
        (by norm_num [cell13062]) (by norm_num [cell13062])
      exact ⟨E.1,E.2.trans (by norm_num [cell13062])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy27 (n := 13062) (by norm_num)
        (q := 1 - (cell13062 ⟨27,by decide⟩).lower)
        (by norm_num [cell13062]) (by norm_num [cell13062])
      exact ⟨E.1,E.2.trans (by norm_num [cell13062])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy28 (n := 13062) (by norm_num)
        (q := 1 - (cell13062 ⟨28,by decide⟩).lower)
        (by norm_num [cell13062]) (by norm_num [cell13062])
      exact ⟨E.1,E.2.trans (by norm_num [cell13062])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy29 (n := 13062) (by norm_num)
        (q := 1 - (cell13062 ⟨29,by decide⟩).lower)
        (by norm_num [cell13062]) (by norm_num [cell13062])
      exact ⟨E.1,E.2.trans (by norm_num [cell13062])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy30 (n := 13062) (by norm_num)
        (q := 1 - (cell13062 ⟨30,by decide⟩).lower)
        (by norm_num [cell13062]) (by norm_num [cell13062])
      exact ⟨E.1,E.2.trans (by norm_num [cell13062])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy31 (n := 13062) (by norm_num)
        (q := 1 - (cell13062 ⟨31,by decide⟩).lower)
        (by norm_num [cell13062]) (by norm_num [cell13062])
      exact ⟨E.1,E.2.trans (by norm_num [cell13062])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy32 (n := 13062) (by norm_num)
        (q := 1 - (cell13062 ⟨32,by decide⟩).lower)
        (by norm_num [cell13062]) (by norm_num [cell13062])
      exact ⟨E.1,E.2.trans (by norm_num [cell13062])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy33 (n := 13062) (by norm_num)
        (q := 1 - (cell13062 ⟨33,by decide⟩).lower)
        (by norm_num [cell13062]) (by norm_num [cell13062])
      exact ⟨E.1,E.2.trans (by norm_num [cell13062])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy34 (n := 13062) (by norm_num)
        (q := 1 - (cell13062 ⟨34,by decide⟩).lower)
        (by norm_num [cell13062]) (by norm_num [cell13062])
      exact ⟨E.1,E.2.trans (by norm_num [cell13062])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy35 (n := 13062) (by norm_num)
        (q := 1 - (cell13062 ⟨35,by decide⟩).lower)
        (by norm_num [cell13062]) (by norm_num [cell13062])
      exact ⟨E.1,E.2.trans (by norm_num [cell13062])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy36 (n := 13062) (by norm_num)
        (q := 1 - (cell13062 ⟨36,by decide⟩).lower)
        (by norm_num [cell13062]) (by norm_num [cell13062])
      exact ⟨E.1,E.2.trans (by norm_num [cell13062])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy37 (n := 13062) (by norm_num)
        (q := 1 - (cell13062 ⟨37,by decide⟩).lower)
        (by norm_num [cell13062]) (by norm_num [cell13062])
      exact ⟨E.1,E.2.trans (by norm_num [cell13062])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy38 (n := 13062) (by norm_num)
        (q := 1 - (cell13062 ⟨38,by decide⟩).lower)
        (by norm_num [cell13062]) (by norm_num [cell13062])
      exact ⟨E.1,E.2.trans (by norm_num [cell13062])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy39 (n := 13062) (by norm_num)
        (q := 1 - (cell13062 ⟨39,by decide⟩).lower)
        (by norm_num [cell13062]) (by norm_num [cell13062])
      exact ⟨E.1,E.2.trans (by norm_num [cell13062])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy40 (n := 13062) (by norm_num)
        (q := 1 - (cell13062 ⟨40,by decide⟩).lower)
        (by norm_num [cell13062]) (by norm_num [cell13062])
      exact ⟨E.1,E.2.trans (by norm_num [cell13062])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy41 (n := 13062) (by norm_num)
        (q := 1 - (cell13062 ⟨41,by decide⟩).lower)
        (by norm_num [cell13062]) (by norm_num [cell13062])
      exact ⟨E.1,E.2.trans (by norm_num [cell13062])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy42 (n := 13062) (by norm_num)
        (q := 1 - (cell13062 ⟨42,by decide⟩).lower)
        (by norm_num [cell13062]) (by norm_num [cell13062])
      exact ⟨E.1,E.2.trans (by norm_num [cell13062])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy43 (n := 13062) (by norm_num)
        (q := 1 - (cell13062 ⟨43,by decide⟩).lower)
        (by norm_num [cell13062]) (by norm_num [cell13062])
      exact ⟨E.1,E.2.trans (by norm_num [cell13062])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy44 (n := 13062) (by norm_num)
        (q := 1 - (cell13062 ⟨44,by decide⟩).lower)
        (by norm_num [cell13062]) (by norm_num [cell13062])
      exact ⟨E.1,E.2.trans (by norm_num [cell13062])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy45 (n := 13062) (by norm_num)
        (q := 1 - (cell13062 ⟨45,by decide⟩).lower)
        (by norm_num [cell13062]) (by norm_num [cell13062])
      exact ⟨E.1,E.2.trans (by norm_num [cell13062])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy46 (n := 13062) (by norm_num)
        (q := 1 - (cell13062 ⟨46,by decide⟩).lower)
        (by norm_num [cell13062]) (by norm_num [cell13062])
      exact ⟨E.1,E.2.trans (by norm_num [cell13062])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy47 (n := 13062) (by norm_num)
        (q := 1 - (cell13062 ⟨47,by decide⟩).lower)
        (by norm_num [cell13062]) (by norm_num [cell13062])
      exact ⟨E.1,E.2.trans (by norm_num [cell13062])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy48 (n := 13062) (by norm_num)
        (q := 1 - (cell13062 ⟨48,by decide⟩).lower)
        (by norm_num [cell13062]) (by norm_num [cell13062])
      exact ⟨E.1,E.2.trans (by norm_num [cell13062])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy49 (n := 13062) (by norm_num)
        (q := 1 - (cell13062 ⟨49,by decide⟩).lower)
        (by norm_num [cell13062]) (by norm_num [cell13062])
      exact ⟨E.1,E.2.trans (by norm_num [cell13062])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy50 (n := 13062) (by norm_num)
        (q := 1 - (cell13062 ⟨50,by decide⟩).lower)
        (by norm_num [cell13062]) (by norm_num [cell13062])
      exact ⟨E.1,E.2.trans (by norm_num [cell13062])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy51 (n := 13062) (by norm_num)
        (q := 1 - (cell13062 ⟨51,by decide⟩).lower)
        (by norm_num [cell13062]) (by norm_num [cell13062])
      exact ⟨E.1,E.2.trans (by norm_num [cell13062])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy52 (n := 13062) (by norm_num)
        (q := 1 - (cell13062 ⟨52,by decide⟩).lower)
        (by norm_num [cell13062]) (by norm_num [cell13062])
      exact ⟨E.1,E.2.trans (by norm_num [cell13062])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13062

/-! Source-cell containment and simple scalar guards at 13062. -/
namespace BstLean.Part269.N13062
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13062)
open BstLean.Part268 (cell13062)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13062 ⟨10,by decide⟩).lower ∧ (cell13062 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13062 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13062 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13062 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13062 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13062 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13062,cell13062,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13062 ⟨11,by decide⟩).lower ∧ (cell13062 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13062 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13062 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13062 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13062 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13062 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13062,cell13062,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13062 ⟨12,by decide⟩).lower ∧ (cell13062 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13062 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13062 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13062 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13062 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13062 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13062,cell13062,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13062 ⟨13,by decide⟩).lower ∧ (cell13062 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13062 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13062 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13062 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13062 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13062 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13062,cell13062,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13062 ⟨14,by decide⟩).lower ∧ (cell13062 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13062 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13062 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13062 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13062 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13062 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13062,cell13062,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13062 ⟨15,by decide⟩).lower ∧ (cell13062 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13062 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13062 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13062 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13062 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13062 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13062,cell13062,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13062 ⟨16,by decide⟩).lower ∧ (cell13062 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13062 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13062 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13062 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13062 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13062 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13062,cell13062,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13062 ⟨17,by decide⟩).lower ∧ (cell13062 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13062 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13062 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13062 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13062 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13062 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13062,cell13062,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13062 ⟨18,by decide⟩).lower ∧ (cell13062 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13062 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13062 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13062 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13062 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13062 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13062,cell13062,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13062 ⟨19,by decide⟩).lower ∧ (cell13062 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13062 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13062 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13062 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13062 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13062 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13062,cell13062,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13062 ⟨20,by decide⟩).lower ∧ (cell13062 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13062 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13062 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13062 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13062 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13062 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13062,cell13062,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13062 ⟨21,by decide⟩).lower ∧ (cell13062 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13062 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13062 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13062 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13062 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13062 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13062,cell13062,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13062 ⟨22,by decide⟩).lower ∧ (cell13062 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13062 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13062 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13062 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13062 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13062 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13062,cell13062,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13062 ⟨23,by decide⟩).lower ∧ (cell13062 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13062 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13062 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13062 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13062 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13062 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13062,cell13062,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13062 ⟨24,by decide⟩).lower ∧ (cell13062 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13062 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13062 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13062 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13062 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13062 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13062,cell13062,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13062 ⟨25,by decide⟩).lower ∧ (cell13062 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13062 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13062 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13062 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13062 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13062 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13062,cell13062,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13062 ⟨26,by decide⟩).lower ∧ (cell13062 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13062 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13062 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13062 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13062 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13062 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13062,cell13062,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13062 ⟨27,by decide⟩).lower ∧ (cell13062 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13062 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13062 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13062 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13062 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13062 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13062,cell13062,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13062 ⟨28,by decide⟩).lower ∧ (cell13062 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13062 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13062 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13062 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13062 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13062 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13062,cell13062,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13062 ⟨29,by decide⟩).lower ∧ (cell13062 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13062 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13062 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13062 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13062 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13062 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13062,cell13062,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13062 ⟨30,by decide⟩).lower ∧ (cell13062 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13062 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13062 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13062 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13062 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13062 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13062,cell13062,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13062 ⟨31,by decide⟩).lower ∧ (cell13062 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13062 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13062 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13062 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13062 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13062 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13062,cell13062,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13062 ⟨32,by decide⟩).lower ∧ (cell13062 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13062 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13062 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13062 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13062 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13062 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13062,cell13062,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13062 ⟨33,by decide⟩).lower ∧ (cell13062 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13062 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13062 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13062 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13062 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13062 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13062,cell13062,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13062 ⟨34,by decide⟩).lower ∧ (cell13062 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13062 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13062 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13062 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13062 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13062 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13062,cell13062,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13062 ⟨35,by decide⟩).lower ∧ (cell13062 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13062 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13062 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13062 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13062 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13062 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13062,cell13062,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13062 ⟨36,by decide⟩).lower ∧ (cell13062 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13062 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13062 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13062 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13062 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13062 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13062,cell13062,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13062 ⟨37,by decide⟩).lower ∧ (cell13062 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13062 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13062 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13062 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13062 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13062 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13062,cell13062,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13062 ⟨38,by decide⟩).lower ∧ (cell13062 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13062 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13062 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13062 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13062 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13062 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13062,cell13062,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13062 ⟨39,by decide⟩).lower ∧ (cell13062 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13062 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13062 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13062 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13062 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13062 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13062,cell13062,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13062 ⟨40,by decide⟩).lower ∧ (cell13062 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13062 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13062 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13062 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13062 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13062 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13062,cell13062,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13062 ⟨41,by decide⟩).lower ∧ (cell13062 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13062 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13062 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13062 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13062 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13062 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13062,cell13062,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13062 ⟨42,by decide⟩).lower ∧ (cell13062 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13062 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13062 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13062 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13062 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13062 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13062,cell13062,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13062 ⟨43,by decide⟩).lower ∧ (cell13062 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13062 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13062 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13062 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13062 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13062 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13062,cell13062,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13062 ⟨44,by decide⟩).lower ∧ (cell13062 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13062 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13062 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13062 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13062 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13062 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13062,cell13062,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13062 ⟨45,by decide⟩).lower ∧ (cell13062 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13062 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13062 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13062 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13062 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13062 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13062,cell13062,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13062 ⟨46,by decide⟩).lower ∧ (cell13062 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13062 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13062 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13062 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13062 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13062 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13062,cell13062,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13062 ⟨47,by decide⟩).lower ∧ (cell13062 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13062 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13062 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13062 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13062 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13062 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13062,cell13062,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13062 ⟨48,by decide⟩).lower ∧ (cell13062 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13062 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13062 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13062 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13062 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13062 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13062,cell13062,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13062 ⟨49,by decide⟩).lower ∧ (cell13062 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13062 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13062 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13062 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13062 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13062 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13062,cell13062,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13062 ⟨50,by decide⟩).lower ∧ (cell13062 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13062 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13062 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13062 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13062 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13062 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13062,cell13062,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13062 ⟨51,by decide⟩).lower ∧ (cell13062 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13062 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13062 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13062 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13062 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13062 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13062,cell13062,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13062 ⟨52,by decide⟩).lower ∧ (cell13062 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13062 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13062 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13062 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13062 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13062 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13062,cell13062,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13062 i).lower ∧
    (cell13062 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13062 i).upper ≤ (0.532 : ℝ) ∧
    (cell13062 i).centre ≤ (0.1 : ℝ) ∧ (cell13062 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13062 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13062 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13062

/-! The local source numeric instances at 13062 have no network premises. -/
namespace BstLean.Part269.N13062
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13062)
open BstLean.Part268 (cell13062)

noncomputable def sourceNumerics13062 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13062 (cell13062 i)
      scalarRow13062.M scalarRow13062.H scalarRow13062.xi := by
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
    energy_allowance := scalarRow13062.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13062]
    centre_nonneg := (scalarRow13062.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D28.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13062])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13062