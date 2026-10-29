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
import BstLean.Part269Direction0
import BstLean.Part269Shared0
import BstLean.Part269Finite
import BstLean.Part269N12350Source
import BstLean.Part269Rows0
import BstLean.Part269Source
/-! Actual 12351 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12351
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12351 ≤ (1.036316104924 : ℝ) := by
  have hr : (111.135052976097 : ℝ) ≤ √(12351 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.135052976097 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12351 12351 (11 / 1000) ≤
    (0.008601130853 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12351) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.135052976097 : ℝ) ≤ √(12351 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12351)
  have hdiv : K / √(12351 : ℝ) ≤ K / 111.135052976097 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.135052976097 ≤ (0.008601130853 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12351.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12351 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12351 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12351 := gPlus_lower 12351
end BstLean.Part269.N12351

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12351
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036316104923 : ℝ) ≤ wn 12351 := by
  have hn : √(12351 : ℝ) ≤ 111.135052976098 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12351 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.135052976098 ≤ 2 / √(12351 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000259124965 : ℝ) ≤ rhoBar 12351 BstLean.Part154.csC ∧
    rhoBar 12351 BstLean.Part154.csC ≤ 0.000259125366 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036316104923 : ℝ) / (1.295212 * 12351) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036316104924 : ℝ) / (1.29521 * 12351) := by gcongr
      _ ≤ (0.000259125366 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12351 BstLean.Part154.csC) ≤ 0.001036568610 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12351 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12351 BstLean.Part154.csC) (piBar (rhoBar 12351 BstLean.Part154.csC)) ≤ 0.000197921967 ∧
    cc1 (rhoBar 12351 BstLean.Part154.csC) (piBar (rhoBar 12351 BstLean.Part154.csC)) ≤ 0.000125939008 ∧
    cc2 (rhoBar 12351 BstLean.Part154.csC) ≤ 0.000073108493 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12351 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12351 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12351 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12351 BstLean.Part154.csC * nuR (rhoBar 12351 BstLean.Part154.csC)) ≤ 0.000518267519 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000259125366 : ℝ) * 0.001036568610 := by gcongr
      _ ≤ (0.000518267519 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12351 BstLean.Part154.csC) * nuR (rhoBar 12351 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001036568610 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12351 BstLean.Part154.csC) * rhoBar 12351 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000259125366 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000259125366 / 2 + 0.399 * 0.001036568610 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000197921967 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000518267519 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125939008 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000259125366 / 1.414213562 := by gcongr
      _ ≤ (0.000073108493 : ℝ) := by norm_num

end BstLean.Part269.N12351

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12351
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12351 BstLean.Part154.csC) (piBar (rhoBar 12351 BstLean.Part154.csC)) ≤ 1.69170E-7 := by
  have hr0 : 0 ≤ rhoBar 12351 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12351 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12351 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12351 BstLean.Part154.csC) (piBar (rhoBar 12351 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12351 BstLean.Part154.csC) (piBar (rhoBar 12351 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12351 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000197921967 : ℝ) ^ 2 + 0.000125939008 ^ 2 + 3 * 0.000073108493 ^ 2 +
        2 * 0.797885 * 0.000197921967 * 0.000125939008 + 2 * 0.000197921967 * 0.000073108493 +
        4 * 0.797885 * 0.000125939008 * 0.000073108493 := by gcongr
    _ ≤ (1.69170E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12351 BstLean.Part154.csC Θ ≤ 0.002706240142 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12351 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12351 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12351 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12351 BstLean.Part154.csC) (piBar (rhoBar 12351 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12351 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036316104924 * 1.69170E-7 / (0.000259124965 : ℝ) := by gcongr
    _ ≤ 0.002706240142 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12351 BstLean.Part154.csC Θ ≤ 0.003004184207 + 0.000683820917 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12351 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12351 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12351 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036316104924 : ℝ) * ((2 * Θ * 0.000259125366 +
        (6863 / 10000) * 0.000259125366 * 12351 * 0.001036568610) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003004184207 + 0.000683820917 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12351 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12351 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12351 0.011 Θ ∧ gammaRatio 12351 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12351 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036316104924 : ℝ) * 0.525 / ((1 - 0.011) * 12351) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12351 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12351 0.011 Θ) :=
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
    badAllowance 12351 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12351 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12351 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12351 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12351 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12351 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12351 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12351 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12351 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12351 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12351 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036316104924 : ℝ) * 12351 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12351 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004104184207 + 0.003390061059 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12351

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12351
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12351 BstLean.Part154.csC) (piBar (rhoBar 12351 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12351 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12351 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12351 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12351 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12351 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12351 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12351 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12351 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12351 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12351 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12351 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12351 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12351 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12351 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053228763858 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12351) ≤ 0.010745822755 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12351 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036316104924)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010745822755 + 2 * 0.737676 / 12351) := by gcongr
    _ ≤ (0.053228763858 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12351 12 ≤ 0.0015 := by
  exact BstLean.Part269.S0.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12351

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12351
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560487339502 : ℝ) ≤ plow 12351 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12351) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053390566263)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001420776075) : eMP 12351 0.011 xi bn ≤ 0.001222709911 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12351 : ℝ) * (1 - 0.011))) ≤ 0.000604489236 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001420776075 / (12351 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000604489236 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000604489236 : ℝ) + 3.141593 * 0.053390566263 / (12351 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001222709911 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053390566263)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001420776075) : PiBarMP 12351 12 0.011 xi bn ≤ 0.163538398970 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12351 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037693183403 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.522119957952 : ℝ) ≤ √((12351 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.135052976097 : ℝ) ≤ √(12351 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12351) ≤ 0.125364661191 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037693183403 + 0.053390566263 * 1.772454 / (2 * (110.522119957952 : ℝ))) * (1 + 0.001222709911) +
        8 / (12351 * 111.135052976097) + 0.125364661191 := by gcongr
    _ ≤ (0.163538398970 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053390566263)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001420776075) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284292751236) :
    parallelOracle 12351 0.011 xi bn cd ≤ 0.164560357380 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12351 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12351 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560487339502 : ℝ) ≤ plow 12351 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.135052976097 : ℝ) ≤ √(12351 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284292751236 : ℝ) / (2 * 0.560487339502 * 111.135052976097)) * 0.163538398970 +
        0.284292751236 ^ 2 / (2 * 0.560487339502 * 111.135052976097) := by gcongr
    _ ≤ (0.164560357380 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053390566263) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001420776075)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284292751236) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12351 12351 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560487339502 : ℝ) ≤ plow 12351 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.135052976097 : ℝ) ≤ √(12351 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12351 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12351 Θ 1.22 ≤ 0.011932333360 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.135052976097 := by gcongr <;> linarith
      _ ≤ (0.011932333360 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12351 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12351 12351 0.011 ≤ 0.008601130853 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12351 12351 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12351 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12351 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12351 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12351 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164560357380 + 0.011932333360 + (0.008601130853 : ℝ) *
        (1 + 2 * (0.284292751236 + 0.011932333360) / (0.560487339502 * 111.135052976097))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12351]

end BstLean.Part269.N12351

/-! The original eight local profiles supply actual 12351 moment certificates. -/
namespace BstLean.Part269.N12351
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12351 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12351 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12351 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053390566263 ∧
    0 ≤ bN 12351 BstLean.Part154.csC (groupTheta g) ∧ bN 12351 BstLean.Part154.csC (groupTheta g) ≤ 0.001420776075 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12351 12351 0.011
      (momentAllowance 12351 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12351 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12351 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12351 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12351 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12351 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231063987378 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12351 0.011
      (momentAllowance 12351 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12351 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12351
/-! The actual computed-centre upper energy formula at 12351. -/
namespace BstLean.Part269.N12351
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12351

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12351
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12351)
open BstLean.Part268 (cell12351)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086582798387
  | 2 => 0.087547418258
  | 3 => 0.088513648685
  | 4 => 0.089483684657
  | 5 => 0.090460151534
  | 6 => 0.091446164999
  | 7 => 0.092445395934
  | 8 => 0.093462140168
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12351 12351 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12351 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004104440387 + 0.003390347157 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S0.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12351

/-! Actual upper energy certificates on all 43 source endpoints at 12351. -/
namespace BstLean.Part269.N12351
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12351)
open BstLean.Part268 (cell12351)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12351 (gMinus 12351) (1 - (cell12351 i).lower) ≤ 1 ∧
    energyUpper 12351 (gMinus 12351) (BstLean.Part211.gPlus 12351)
      (finiteEnergy 12351 12351 0.011) (1 - (cell12351 i).lower) ≤
      (cell12351 i).energy := by
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
      have E := BstLean.Part269.S0.uniformEnergy10 (n := 12351) (by norm_num)
        (q := 1 - (cell12351 ⟨10,by decide⟩).lower)
        (by norm_num [cell12351]) (by norm_num [cell12351])
      exact ⟨E.1,E.2.trans (by norm_num [cell12351])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy11 (n := 12351) (by norm_num)
        (q := 1 - (cell12351 ⟨11,by decide⟩).lower)
        (by norm_num [cell12351]) (by norm_num [cell12351])
      exact ⟨E.1,E.2.trans (by norm_num [cell12351])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy12 (n := 12351) (by norm_num)
        (q := 1 - (cell12351 ⟨12,by decide⟩).lower)
        (by norm_num [cell12351]) (by norm_num [cell12351])
      exact ⟨E.1,E.2.trans (by norm_num [cell12351])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy13 (n := 12351) (by norm_num)
        (q := 1 - (cell12351 ⟨13,by decide⟩).lower)
        (by norm_num [cell12351]) (by norm_num [cell12351])
      exact ⟨E.1,E.2.trans (by norm_num [cell12351])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy14 (n := 12351) (by norm_num)
        (q := 1 - (cell12351 ⟨14,by decide⟩).lower)
        (by norm_num [cell12351]) (by norm_num [cell12351])
      exact ⟨E.1,E.2.trans (by norm_num [cell12351])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy15 (n := 12351) (by norm_num)
        (q := 1 - (cell12351 ⟨15,by decide⟩).lower)
        (by norm_num [cell12351]) (by norm_num [cell12351])
      exact ⟨E.1,E.2.trans (by norm_num [cell12351])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy16 (n := 12351) (by norm_num)
        (q := 1 - (cell12351 ⟨16,by decide⟩).lower)
        (by norm_num [cell12351]) (by norm_num [cell12351])
      exact ⟨E.1,E.2.trans (by norm_num [cell12351])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy17 (n := 12351) (by norm_num)
        (q := 1 - (cell12351 ⟨17,by decide⟩).lower)
        (by norm_num [cell12351]) (by norm_num [cell12351])
      exact ⟨E.1,E.2.trans (by norm_num [cell12351])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy18 (n := 12351) (by norm_num)
        (q := 1 - (cell12351 ⟨18,by decide⟩).lower)
        (by norm_num [cell12351]) (by norm_num [cell12351])
      exact ⟨E.1,E.2.trans (by norm_num [cell12351])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy19 (n := 12351) (by norm_num)
        (q := 1 - (cell12351 ⟨19,by decide⟩).lower)
        (by norm_num [cell12351]) (by norm_num [cell12351])
      exact ⟨E.1,E.2.trans (by norm_num [cell12351])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy20 (n := 12351) (by norm_num)
        (q := 1 - (cell12351 ⟨20,by decide⟩).lower)
        (by norm_num [cell12351]) (by norm_num [cell12351])
      exact ⟨E.1,E.2.trans (by norm_num [cell12351])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy21 (n := 12351) (by norm_num)
        (q := 1 - (cell12351 ⟨21,by decide⟩).lower)
        (by norm_num [cell12351]) (by norm_num [cell12351])
      exact ⟨E.1,E.2.trans (by norm_num [cell12351])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy22 (n := 12351) (by norm_num)
        (q := 1 - (cell12351 ⟨22,by decide⟩).lower)
        (by norm_num [cell12351]) (by norm_num [cell12351])
      exact ⟨E.1,E.2.trans (by norm_num [cell12351])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy23 (n := 12351) (by norm_num)
        (q := 1 - (cell12351 ⟨23,by decide⟩).lower)
        (by norm_num [cell12351]) (by norm_num [cell12351])
      exact ⟨E.1,E.2.trans (by norm_num [cell12351])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy24 (n := 12351) (by norm_num)
        (q := 1 - (cell12351 ⟨24,by decide⟩).lower)
        (by norm_num [cell12351]) (by norm_num [cell12351])
      exact ⟨E.1,E.2.trans (by norm_num [cell12351])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy25 (n := 12351) (by norm_num)
        (q := 1 - (cell12351 ⟨25,by decide⟩).lower)
        (by norm_num [cell12351]) (by norm_num [cell12351])
      exact ⟨E.1,E.2.trans (by norm_num [cell12351])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy26 (n := 12351) (by norm_num)
        (q := 1 - (cell12351 ⟨26,by decide⟩).lower)
        (by norm_num [cell12351]) (by norm_num [cell12351])
      exact ⟨E.1,E.2.trans (by norm_num [cell12351])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy27 (n := 12351) (by norm_num)
        (q := 1 - (cell12351 ⟨27,by decide⟩).lower)
        (by norm_num [cell12351]) (by norm_num [cell12351])
      exact ⟨E.1,E.2.trans (by norm_num [cell12351])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy28 (n := 12351) (by norm_num)
        (q := 1 - (cell12351 ⟨28,by decide⟩).lower)
        (by norm_num [cell12351]) (by norm_num [cell12351])
      exact ⟨E.1,E.2.trans (by norm_num [cell12351])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy29 (n := 12351) (by norm_num)
        (q := 1 - (cell12351 ⟨29,by decide⟩).lower)
        (by norm_num [cell12351]) (by norm_num [cell12351])
      exact ⟨E.1,E.2.trans (by norm_num [cell12351])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy30 (n := 12351) (by norm_num)
        (q := 1 - (cell12351 ⟨30,by decide⟩).lower)
        (by norm_num [cell12351]) (by norm_num [cell12351])
      exact ⟨E.1,E.2.trans (by norm_num [cell12351])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy31 (n := 12351) (by norm_num)
        (q := 1 - (cell12351 ⟨31,by decide⟩).lower)
        (by norm_num [cell12351]) (by norm_num [cell12351])
      exact ⟨E.1,E.2.trans (by norm_num [cell12351])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy32 (n := 12351) (by norm_num)
        (q := 1 - (cell12351 ⟨32,by decide⟩).lower)
        (by norm_num [cell12351]) (by norm_num [cell12351])
      exact ⟨E.1,E.2.trans (by norm_num [cell12351])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy33 (n := 12351) (by norm_num)
        (q := 1 - (cell12351 ⟨33,by decide⟩).lower)
        (by norm_num [cell12351]) (by norm_num [cell12351])
      exact ⟨E.1,E.2.trans (by norm_num [cell12351])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy34 (n := 12351) (by norm_num)
        (q := 1 - (cell12351 ⟨34,by decide⟩).lower)
        (by norm_num [cell12351]) (by norm_num [cell12351])
      exact ⟨E.1,E.2.trans (by norm_num [cell12351])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy35 (n := 12351) (by norm_num)
        (q := 1 - (cell12351 ⟨35,by decide⟩).lower)
        (by norm_num [cell12351]) (by norm_num [cell12351])
      exact ⟨E.1,E.2.trans (by norm_num [cell12351])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy36 (n := 12351) (by norm_num)
        (q := 1 - (cell12351 ⟨36,by decide⟩).lower)
        (by norm_num [cell12351]) (by norm_num [cell12351])
      exact ⟨E.1,E.2.trans (by norm_num [cell12351])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy37 (n := 12351) (by norm_num)
        (q := 1 - (cell12351 ⟨37,by decide⟩).lower)
        (by norm_num [cell12351]) (by norm_num [cell12351])
      exact ⟨E.1,E.2.trans (by norm_num [cell12351])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy38 (n := 12351) (by norm_num)
        (q := 1 - (cell12351 ⟨38,by decide⟩).lower)
        (by norm_num [cell12351]) (by norm_num [cell12351])
      exact ⟨E.1,E.2.trans (by norm_num [cell12351])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy39 (n := 12351) (by norm_num)
        (q := 1 - (cell12351 ⟨39,by decide⟩).lower)
        (by norm_num [cell12351]) (by norm_num [cell12351])
      exact ⟨E.1,E.2.trans (by norm_num [cell12351])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy40 (n := 12351) (by norm_num)
        (q := 1 - (cell12351 ⟨40,by decide⟩).lower)
        (by norm_num [cell12351]) (by norm_num [cell12351])
      exact ⟨E.1,E.2.trans (by norm_num [cell12351])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy41 (n := 12351) (by norm_num)
        (q := 1 - (cell12351 ⟨41,by decide⟩).lower)
        (by norm_num [cell12351]) (by norm_num [cell12351])
      exact ⟨E.1,E.2.trans (by norm_num [cell12351])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy42 (n := 12351) (by norm_num)
        (q := 1 - (cell12351 ⟨42,by decide⟩).lower)
        (by norm_num [cell12351]) (by norm_num [cell12351])
      exact ⟨E.1,E.2.trans (by norm_num [cell12351])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy43 (n := 12351) (by norm_num)
        (q := 1 - (cell12351 ⟨43,by decide⟩).lower)
        (by norm_num [cell12351]) (by norm_num [cell12351])
      exact ⟨E.1,E.2.trans (by norm_num [cell12351])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy44 (n := 12351) (by norm_num)
        (q := 1 - (cell12351 ⟨44,by decide⟩).lower)
        (by norm_num [cell12351]) (by norm_num [cell12351])
      exact ⟨E.1,E.2.trans (by norm_num [cell12351])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy45 (n := 12351) (by norm_num)
        (q := 1 - (cell12351 ⟨45,by decide⟩).lower)
        (by norm_num [cell12351]) (by norm_num [cell12351])
      exact ⟨E.1,E.2.trans (by norm_num [cell12351])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy46 (n := 12351) (by norm_num)
        (q := 1 - (cell12351 ⟨46,by decide⟩).lower)
        (by norm_num [cell12351]) (by norm_num [cell12351])
      exact ⟨E.1,E.2.trans (by norm_num [cell12351])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy47 (n := 12351) (by norm_num)
        (q := 1 - (cell12351 ⟨47,by decide⟩).lower)
        (by norm_num [cell12351]) (by norm_num [cell12351])
      exact ⟨E.1,E.2.trans (by norm_num [cell12351])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy48 (n := 12351) (by norm_num)
        (q := 1 - (cell12351 ⟨48,by decide⟩).lower)
        (by norm_num [cell12351]) (by norm_num [cell12351])
      exact ⟨E.1,E.2.trans (by norm_num [cell12351])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy49 (n := 12351) (by norm_num)
        (q := 1 - (cell12351 ⟨49,by decide⟩).lower)
        (by norm_num [cell12351]) (by norm_num [cell12351])
      exact ⟨E.1,E.2.trans (by norm_num [cell12351])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy50 (n := 12351) (by norm_num)
        (q := 1 - (cell12351 ⟨50,by decide⟩).lower)
        (by norm_num [cell12351]) (by norm_num [cell12351])
      exact ⟨E.1,E.2.trans (by norm_num [cell12351])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy51 (n := 12351) (by norm_num)
        (q := 1 - (cell12351 ⟨51,by decide⟩).lower)
        (by norm_num [cell12351]) (by norm_num [cell12351])
      exact ⟨E.1,E.2.trans (by norm_num [cell12351])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy52 (n := 12351) (by norm_num)
        (q := 1 - (cell12351 ⟨52,by decide⟩).lower)
        (by norm_num [cell12351]) (by norm_num [cell12351])
      exact ⟨E.1,E.2.trans (by norm_num [cell12351])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12351

/-! Source-cell containment and simple scalar guards at 12351. -/
namespace BstLean.Part269.N12351
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12351)
open BstLean.Part268 (cell12351)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12351 ⟨10,by decide⟩).lower ∧ (cell12351 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12351 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12351 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12351 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12351 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12351 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12351,cell12351,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12351 ⟨11,by decide⟩).lower ∧ (cell12351 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12351 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12351 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12351 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12351 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12351 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12351,cell12351,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12351 ⟨12,by decide⟩).lower ∧ (cell12351 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12351 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12351 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12351 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12351 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12351 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12351,cell12351,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12351 ⟨13,by decide⟩).lower ∧ (cell12351 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12351 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12351 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12351 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12351 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12351 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12351,cell12351,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12351 ⟨14,by decide⟩).lower ∧ (cell12351 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12351 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12351 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12351 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12351 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12351 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12351,cell12351,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12351 ⟨15,by decide⟩).lower ∧ (cell12351 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12351 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12351 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12351 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12351 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12351 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12351,cell12351,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12351 ⟨16,by decide⟩).lower ∧ (cell12351 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12351 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12351 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12351 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12351 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12351 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12351,cell12351,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12351 ⟨17,by decide⟩).lower ∧ (cell12351 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12351 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12351 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12351 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12351 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12351 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12351,cell12351,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12351 ⟨18,by decide⟩).lower ∧ (cell12351 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12351 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12351 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12351 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12351 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12351 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12351,cell12351,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12351 ⟨19,by decide⟩).lower ∧ (cell12351 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12351 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12351 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12351 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12351 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12351 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12351,cell12351,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12351 ⟨20,by decide⟩).lower ∧ (cell12351 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12351 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12351 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12351 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12351 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12351 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12351,cell12351,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12351 ⟨21,by decide⟩).lower ∧ (cell12351 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12351 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12351 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12351 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12351 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12351 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12351,cell12351,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12351 ⟨22,by decide⟩).lower ∧ (cell12351 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12351 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12351 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12351 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12351 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12351 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12351,cell12351,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12351 ⟨23,by decide⟩).lower ∧ (cell12351 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12351 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12351 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12351 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12351 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12351 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12351,cell12351,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12351 ⟨24,by decide⟩).lower ∧ (cell12351 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12351 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12351 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12351 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12351 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12351 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12351,cell12351,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12351 ⟨25,by decide⟩).lower ∧ (cell12351 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12351 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12351 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12351 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12351 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12351 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12351,cell12351,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12351 ⟨26,by decide⟩).lower ∧ (cell12351 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12351 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12351 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12351 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12351 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12351 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12351,cell12351,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12351 ⟨27,by decide⟩).lower ∧ (cell12351 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12351 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12351 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12351 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12351 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12351 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12351,cell12351,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12351 ⟨28,by decide⟩).lower ∧ (cell12351 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12351 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12351 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12351 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12351 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12351 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12351,cell12351,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12351 ⟨29,by decide⟩).lower ∧ (cell12351 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12351 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12351 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12351 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12351 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12351 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12351,cell12351,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12351 ⟨30,by decide⟩).lower ∧ (cell12351 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12351 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12351 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12351 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12351 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12351 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12351,cell12351,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12351 ⟨31,by decide⟩).lower ∧ (cell12351 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12351 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12351 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12351 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12351 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12351 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12351,cell12351,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12351 ⟨32,by decide⟩).lower ∧ (cell12351 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12351 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12351 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12351 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12351 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12351 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12351,cell12351,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12351 ⟨33,by decide⟩).lower ∧ (cell12351 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12351 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12351 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12351 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12351 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12351 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12351,cell12351,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12351 ⟨34,by decide⟩).lower ∧ (cell12351 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12351 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12351 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12351 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12351 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12351 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12351,cell12351,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12351 ⟨35,by decide⟩).lower ∧ (cell12351 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12351 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12351 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12351 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12351 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12351 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12351,cell12351,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12351 ⟨36,by decide⟩).lower ∧ (cell12351 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12351 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12351 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12351 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12351 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12351 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12351,cell12351,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12351 ⟨37,by decide⟩).lower ∧ (cell12351 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12351 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12351 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12351 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12351 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12351 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12351,cell12351,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12351 ⟨38,by decide⟩).lower ∧ (cell12351 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12351 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12351 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12351 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12351 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12351 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12351,cell12351,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12351 ⟨39,by decide⟩).lower ∧ (cell12351 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12351 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12351 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12351 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12351 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12351 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12351,cell12351,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12351 ⟨40,by decide⟩).lower ∧ (cell12351 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12351 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12351 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12351 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12351 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12351 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12351,cell12351,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12351 ⟨41,by decide⟩).lower ∧ (cell12351 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12351 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12351 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12351 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12351 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12351 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12351,cell12351,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12351 ⟨42,by decide⟩).lower ∧ (cell12351 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12351 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12351 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12351 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12351 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12351 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12351,cell12351,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12351 ⟨43,by decide⟩).lower ∧ (cell12351 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12351 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12351 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12351 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12351 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12351 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12351,cell12351,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12351 ⟨44,by decide⟩).lower ∧ (cell12351 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12351 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12351 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12351 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12351 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12351 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12351,cell12351,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12351 ⟨45,by decide⟩).lower ∧ (cell12351 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12351 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12351 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12351 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12351 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12351 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12351,cell12351,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12351 ⟨46,by decide⟩).lower ∧ (cell12351 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12351 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12351 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12351 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12351 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12351 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12351,cell12351,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12351 ⟨47,by decide⟩).lower ∧ (cell12351 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12351 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12351 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12351 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12351 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12351 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12351,cell12351,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12351 ⟨48,by decide⟩).lower ∧ (cell12351 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12351 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12351 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12351 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12351 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12351 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12351,cell12351,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12351 ⟨49,by decide⟩).lower ∧ (cell12351 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12351 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12351 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12351 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12351 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12351 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12351,cell12351,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12351 ⟨50,by decide⟩).lower ∧ (cell12351 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12351 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12351 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12351 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12351 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12351 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12351,cell12351,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12351 ⟨51,by decide⟩).lower ∧ (cell12351 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12351 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12351 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12351 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12351 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12351 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12351,cell12351,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12351 ⟨52,by decide⟩).lower ∧ (cell12351 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12351 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12351 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12351 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12351 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12351 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12351,cell12351,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12351 i).lower ∧
    (cell12351 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12351 i).upper ≤ (0.532 : ℝ) ∧
    (cell12351 i).centre ≤ (0.1 : ℝ) ∧ (cell12351 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12351 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12351 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12351

/-! The local source numeric instances at 12351 have no network premises. -/
namespace BstLean.Part269.N12351
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12351)
open BstLean.Part268 (cell12351)

noncomputable def sourceNumerics12351 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12351 (cell12351 i)
      scalarRow12351.M scalarRow12351.H scalarRow12351.xi := by
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
    energy_allowance := scalarRow12351.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12351]
    centre_nonneg := (scalarRow12351.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D0.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12351])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12351
/-! Actual 12352 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12352
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12352 ≤ (1.036314621735 : ℝ) := by
  have hr : (111.139551915598 : ℝ) ≤ √(12352 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.139551915598 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12352 12352 (11 / 1000) ≤
    (0.008600782675 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12352) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.139551915598 : ℝ) ≤ √(12352 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12352)
  have hdiv : K / √(12352 : ℝ) ≤ K / 111.139551915598 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.139551915598 ≤ (0.008600782675 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12352.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12352 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12352 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12352 := gPlus_lower 12352
end BstLean.Part269.N12352

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12352
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036314621734 : ℝ) ≤ wn 12352 := by
  have hn : √(12352 : ℝ) ≤ 111.139551915599 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12352 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.139551915599 ≤ 2 / √(12352 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000259103616 : ℝ) ≤ rhoBar 12352 BstLean.Part154.csC ∧
    rhoBar 12352 BstLean.Part154.csC ≤ 0.000259104017 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036314621734 : ℝ) / (1.295212 * 12352) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036314621735 : ℝ) / (1.29521 * 12352) := by gcongr
      _ ≤ (0.000259104017 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12352 BstLean.Part154.csC) ≤ 0.001036483203 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12352 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12352 BstLean.Part154.csC) (piBar (rhoBar 12352 BstLean.Part154.csC)) ≤ 0.000197905660 ∧
    cc1 (rhoBar 12352 BstLean.Part154.csC) (piBar (rhoBar 12352 BstLean.Part154.csC)) ≤ 0.000125928631 ∧
    cc2 (rhoBar 12352 BstLean.Part154.csC) ≤ 0.000073102469 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12352 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12352 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12352 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12352 BstLean.Part154.csC * nuR (rhoBar 12352 BstLean.Part154.csC)) ≤ 0.000518224818 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000259104017 : ℝ) * 0.001036483203 := by gcongr
      _ ≤ (0.000518224818 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12352 BstLean.Part154.csC) * nuR (rhoBar 12352 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001036483203 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12352 BstLean.Part154.csC) * rhoBar 12352 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000259104017 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000259104017 / 2 + 0.399 * 0.001036483203 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000197905660 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000518224818 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125928631 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000259104017 / 1.414213562 := by gcongr
      _ ≤ (0.000073102469 : ℝ) := by norm_num

end BstLean.Part269.N12352

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12352
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12352 BstLean.Part154.csC) (piBar (rhoBar 12352 BstLean.Part154.csC)) ≤ 1.69142E-7 := by
  have hr0 : 0 ≤ rhoBar 12352 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12352 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12352 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12352 BstLean.Part154.csC) (piBar (rhoBar 12352 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12352 BstLean.Part154.csC) (piBar (rhoBar 12352 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12352 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000197905660 : ℝ) ^ 2 + 0.000125928631 ^ 2 + 3 * 0.000073102469 ^ 2 +
        2 * 0.797885 * 0.000197905660 * 0.000125928631 + 2 * 0.000197905660 * 0.000073102469 +
        4 * 0.797885 * 0.000125928631 * 0.000073102469 := by gcongr
    _ ≤ (1.69142E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12352 BstLean.Part154.csC Θ ≤ 0.002706011294 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12352 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12352 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12352 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12352 BstLean.Part154.csC) (piBar (rhoBar 12352 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12352 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036314621735 * 1.69142E-7 / (0.000259103616 : ℝ) := by gcongr
    _ ≤ 0.002706011294 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12352 BstLean.Part154.csC Θ ≤ 0.003003928085 + 0.000683763599 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12352 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12352 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12352 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036314621735 : ℝ) * ((2 * Θ * 0.000259104017 +
        (6863 / 10000) * 0.000259104017 * 12352 * 0.001036483203) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003003928085 + 0.000683763599 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12352 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12352 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12352 0.011 Θ ∧ gammaRatio 12352 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12352 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036314621735 : ℝ) * 0.525 / ((1 - 0.011) * 12352) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12352 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12352 0.011 Θ) :=
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
    badAllowance 12352 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12352 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12352 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12352 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12352 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12352 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12352 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12352 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12352 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12352 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12352 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036314621735 : ℝ) * 12352 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12352 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004103928085 + 0.003389774893 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12352

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12352
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12352 BstLean.Part154.csC) (piBar (rhoBar 12352 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12352 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12352 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12352 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12352 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12352 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12352 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12352 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12352 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12352 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12352 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12352 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12352 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12352 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12352 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053226585464 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12352) ≤ 0.010745387763 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12352 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036314621735)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010745387763 + 2 * 0.737676 / 12352) := by gcongr
    _ ≤ (0.053226585464 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12352 12 ≤ 0.0015 := by
  exact BstLean.Part269.S0.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12352

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12352
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560487387313 : ℝ) ≤ plow 12352 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12352) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053390159904)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001420655930) : eMP 12352 0.011 xi bn ≤ 0.001222608639 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12352 : ℝ) * (1 - 0.011))) ≤ 0.000604439208 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001420655930 / (12352 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000604439208 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000604439208 : ℝ) + 3.141593 * 0.053390159904 / (12352 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001222608639 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053390159904)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001420655930) : PiBarMP 12352 12 0.011 xi bn ≤ 0.163531703310 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12352 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037691589646 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.526594084862 : ℝ) ≤ √((12352 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.139551915598 : ℝ) ≤ √(12352 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12352) ≤ 0.125359586418 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037691589646 + 0.053390159904 * 1.772454 / (2 * (110.526594084862 : ℝ))) * (1 + 0.001222608639) +
        8 / (12352 * 111.139551915598) + 0.125359586418 := by gcongr
    _ ≤ (0.163531703310 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053390159904)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001420655930) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284289693519) :
    parallelOracle 12352 0.011 xi bn cd ≤ 0.164553587016 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12352 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12352 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560487387313 : ℝ) ≤ plow 12352 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.139551915598 : ℝ) ≤ √(12352 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284289693519 : ℝ) / (2 * 0.560487387313 * 111.139551915598)) * 0.163531703310 +
        0.284289693519 ^ 2 / (2 * 0.560487387313 * 111.139551915598) := by gcongr
    _ ≤ (0.164553587016 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053390159904) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001420655930)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284289693519) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12352 12352 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560487387313 : ℝ) ≤ plow 12352 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.139551915598 : ℝ) ≤ √(12352 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12352 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12352 Θ 1.22 ≤ 0.011931850338 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.139551915598 := by gcongr <;> linarith
      _ ≤ (0.011931850338 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12352 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12352 12352 0.011 ≤ 0.008600782675 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12352 12352 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12352 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12352 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12352 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12352 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164553587016 + 0.011931850338 + (0.008600782675 : ℝ) *
        (1 + 2 * (0.284289693519 + 0.011931850338) / (0.560487387313 * 111.139551915598))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12352]

end BstLean.Part269.N12352

/-! The original eight local profiles supply actual 12352 moment certificates. -/
namespace BstLean.Part269.N12352
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12352 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12352 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12352 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053390159904 ∧
    0 ≤ bN 12352 BstLean.Part154.csC (groupTheta g) ∧ bN 12352 BstLean.Part154.csC (groupTheta g) ≤ 0.001420655930 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12352 12352 0.011
      (momentAllowance 12352 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12352 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12352 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12352 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12352 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12352 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231063108055 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12352 0.011
      (momentAllowance 12352 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12352 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12352
/-! The actual computed-centre upper energy formula at 12352. -/
namespace BstLean.Part269.N12352
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12352

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12352
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12352)
open BstLean.Part268 (cell12352)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086579426391
  | 2 => 0.087543973050
  | 3 => 0.088510117859
  | 4 => 0.089480053096
  | 5 => 0.090456400960
  | 6 => 0.091442273464
  | 7 => 0.092441337269
  | 8 => 0.093457883364
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12352 12352 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12352 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004104440387 + 0.003390347157 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S0.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12352

/-! Actual upper energy certificates on all 43 source endpoints at 12352. -/
namespace BstLean.Part269.N12352
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12352)
open BstLean.Part268 (cell12352)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12352 (gMinus 12352) (1 - (cell12352 i).lower) ≤ 1 ∧
    energyUpper 12352 (gMinus 12352) (BstLean.Part211.gPlus 12352)
      (finiteEnergy 12352 12352 0.011) (1 - (cell12352 i).lower) ≤
      (cell12352 i).energy := by
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
      have E := BstLean.Part269.S0.uniformEnergy10 (n := 12352) (by norm_num)
        (q := 1 - (cell12352 ⟨10,by decide⟩).lower)
        (by norm_num [cell12352]) (by norm_num [cell12352])
      exact ⟨E.1,E.2.trans (by norm_num [cell12352])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy11 (n := 12352) (by norm_num)
        (q := 1 - (cell12352 ⟨11,by decide⟩).lower)
        (by norm_num [cell12352]) (by norm_num [cell12352])
      exact ⟨E.1,E.2.trans (by norm_num [cell12352])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy12 (n := 12352) (by norm_num)
        (q := 1 - (cell12352 ⟨12,by decide⟩).lower)
        (by norm_num [cell12352]) (by norm_num [cell12352])
      exact ⟨E.1,E.2.trans (by norm_num [cell12352])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy13 (n := 12352) (by norm_num)
        (q := 1 - (cell12352 ⟨13,by decide⟩).lower)
        (by norm_num [cell12352]) (by norm_num [cell12352])
      exact ⟨E.1,E.2.trans (by norm_num [cell12352])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy14 (n := 12352) (by norm_num)
        (q := 1 - (cell12352 ⟨14,by decide⟩).lower)
        (by norm_num [cell12352]) (by norm_num [cell12352])
      exact ⟨E.1,E.2.trans (by norm_num [cell12352])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy15 (n := 12352) (by norm_num)
        (q := 1 - (cell12352 ⟨15,by decide⟩).lower)
        (by norm_num [cell12352]) (by norm_num [cell12352])
      exact ⟨E.1,E.2.trans (by norm_num [cell12352])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy16 (n := 12352) (by norm_num)
        (q := 1 - (cell12352 ⟨16,by decide⟩).lower)
        (by norm_num [cell12352]) (by norm_num [cell12352])
      exact ⟨E.1,E.2.trans (by norm_num [cell12352])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy17 (n := 12352) (by norm_num)
        (q := 1 - (cell12352 ⟨17,by decide⟩).lower)
        (by norm_num [cell12352]) (by norm_num [cell12352])
      exact ⟨E.1,E.2.trans (by norm_num [cell12352])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy18 (n := 12352) (by norm_num)
        (q := 1 - (cell12352 ⟨18,by decide⟩).lower)
        (by norm_num [cell12352]) (by norm_num [cell12352])
      exact ⟨E.1,E.2.trans (by norm_num [cell12352])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy19 (n := 12352) (by norm_num)
        (q := 1 - (cell12352 ⟨19,by decide⟩).lower)
        (by norm_num [cell12352]) (by norm_num [cell12352])
      exact ⟨E.1,E.2.trans (by norm_num [cell12352])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy20 (n := 12352) (by norm_num)
        (q := 1 - (cell12352 ⟨20,by decide⟩).lower)
        (by norm_num [cell12352]) (by norm_num [cell12352])
      exact ⟨E.1,E.2.trans (by norm_num [cell12352])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy21 (n := 12352) (by norm_num)
        (q := 1 - (cell12352 ⟨21,by decide⟩).lower)
        (by norm_num [cell12352]) (by norm_num [cell12352])
      exact ⟨E.1,E.2.trans (by norm_num [cell12352])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy22 (n := 12352) (by norm_num)
        (q := 1 - (cell12352 ⟨22,by decide⟩).lower)
        (by norm_num [cell12352]) (by norm_num [cell12352])
      exact ⟨E.1,E.2.trans (by norm_num [cell12352])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy23 (n := 12352) (by norm_num)
        (q := 1 - (cell12352 ⟨23,by decide⟩).lower)
        (by norm_num [cell12352]) (by norm_num [cell12352])
      exact ⟨E.1,E.2.trans (by norm_num [cell12352])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy24 (n := 12352) (by norm_num)
        (q := 1 - (cell12352 ⟨24,by decide⟩).lower)
        (by norm_num [cell12352]) (by norm_num [cell12352])
      exact ⟨E.1,E.2.trans (by norm_num [cell12352])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy25 (n := 12352) (by norm_num)
        (q := 1 - (cell12352 ⟨25,by decide⟩).lower)
        (by norm_num [cell12352]) (by norm_num [cell12352])
      exact ⟨E.1,E.2.trans (by norm_num [cell12352])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy26 (n := 12352) (by norm_num)
        (q := 1 - (cell12352 ⟨26,by decide⟩).lower)
        (by norm_num [cell12352]) (by norm_num [cell12352])
      exact ⟨E.1,E.2.trans (by norm_num [cell12352])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy27 (n := 12352) (by norm_num)
        (q := 1 - (cell12352 ⟨27,by decide⟩).lower)
        (by norm_num [cell12352]) (by norm_num [cell12352])
      exact ⟨E.1,E.2.trans (by norm_num [cell12352])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy28 (n := 12352) (by norm_num)
        (q := 1 - (cell12352 ⟨28,by decide⟩).lower)
        (by norm_num [cell12352]) (by norm_num [cell12352])
      exact ⟨E.1,E.2.trans (by norm_num [cell12352])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy29 (n := 12352) (by norm_num)
        (q := 1 - (cell12352 ⟨29,by decide⟩).lower)
        (by norm_num [cell12352]) (by norm_num [cell12352])
      exact ⟨E.1,E.2.trans (by norm_num [cell12352])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy30 (n := 12352) (by norm_num)
        (q := 1 - (cell12352 ⟨30,by decide⟩).lower)
        (by norm_num [cell12352]) (by norm_num [cell12352])
      exact ⟨E.1,E.2.trans (by norm_num [cell12352])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy31 (n := 12352) (by norm_num)
        (q := 1 - (cell12352 ⟨31,by decide⟩).lower)
        (by norm_num [cell12352]) (by norm_num [cell12352])
      exact ⟨E.1,E.2.trans (by norm_num [cell12352])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy32 (n := 12352) (by norm_num)
        (q := 1 - (cell12352 ⟨32,by decide⟩).lower)
        (by norm_num [cell12352]) (by norm_num [cell12352])
      exact ⟨E.1,E.2.trans (by norm_num [cell12352])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy33 (n := 12352) (by norm_num)
        (q := 1 - (cell12352 ⟨33,by decide⟩).lower)
        (by norm_num [cell12352]) (by norm_num [cell12352])
      exact ⟨E.1,E.2.trans (by norm_num [cell12352])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy34 (n := 12352) (by norm_num)
        (q := 1 - (cell12352 ⟨34,by decide⟩).lower)
        (by norm_num [cell12352]) (by norm_num [cell12352])
      exact ⟨E.1,E.2.trans (by norm_num [cell12352])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy35 (n := 12352) (by norm_num)
        (q := 1 - (cell12352 ⟨35,by decide⟩).lower)
        (by norm_num [cell12352]) (by norm_num [cell12352])
      exact ⟨E.1,E.2.trans (by norm_num [cell12352])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy36 (n := 12352) (by norm_num)
        (q := 1 - (cell12352 ⟨36,by decide⟩).lower)
        (by norm_num [cell12352]) (by norm_num [cell12352])
      exact ⟨E.1,E.2.trans (by norm_num [cell12352])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy37 (n := 12352) (by norm_num)
        (q := 1 - (cell12352 ⟨37,by decide⟩).lower)
        (by norm_num [cell12352]) (by norm_num [cell12352])
      exact ⟨E.1,E.2.trans (by norm_num [cell12352])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy38 (n := 12352) (by norm_num)
        (q := 1 - (cell12352 ⟨38,by decide⟩).lower)
        (by norm_num [cell12352]) (by norm_num [cell12352])
      exact ⟨E.1,E.2.trans (by norm_num [cell12352])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy39 (n := 12352) (by norm_num)
        (q := 1 - (cell12352 ⟨39,by decide⟩).lower)
        (by norm_num [cell12352]) (by norm_num [cell12352])
      exact ⟨E.1,E.2.trans (by norm_num [cell12352])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy40 (n := 12352) (by norm_num)
        (q := 1 - (cell12352 ⟨40,by decide⟩).lower)
        (by norm_num [cell12352]) (by norm_num [cell12352])
      exact ⟨E.1,E.2.trans (by norm_num [cell12352])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy41 (n := 12352) (by norm_num)
        (q := 1 - (cell12352 ⟨41,by decide⟩).lower)
        (by norm_num [cell12352]) (by norm_num [cell12352])
      exact ⟨E.1,E.2.trans (by norm_num [cell12352])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy42 (n := 12352) (by norm_num)
        (q := 1 - (cell12352 ⟨42,by decide⟩).lower)
        (by norm_num [cell12352]) (by norm_num [cell12352])
      exact ⟨E.1,E.2.trans (by norm_num [cell12352])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy43 (n := 12352) (by norm_num)
        (q := 1 - (cell12352 ⟨43,by decide⟩).lower)
        (by norm_num [cell12352]) (by norm_num [cell12352])
      exact ⟨E.1,E.2.trans (by norm_num [cell12352])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy44 (n := 12352) (by norm_num)
        (q := 1 - (cell12352 ⟨44,by decide⟩).lower)
        (by norm_num [cell12352]) (by norm_num [cell12352])
      exact ⟨E.1,E.2.trans (by norm_num [cell12352])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy45 (n := 12352) (by norm_num)
        (q := 1 - (cell12352 ⟨45,by decide⟩).lower)
        (by norm_num [cell12352]) (by norm_num [cell12352])
      exact ⟨E.1,E.2.trans (by norm_num [cell12352])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy46 (n := 12352) (by norm_num)
        (q := 1 - (cell12352 ⟨46,by decide⟩).lower)
        (by norm_num [cell12352]) (by norm_num [cell12352])
      exact ⟨E.1,E.2.trans (by norm_num [cell12352])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy47 (n := 12352) (by norm_num)
        (q := 1 - (cell12352 ⟨47,by decide⟩).lower)
        (by norm_num [cell12352]) (by norm_num [cell12352])
      exact ⟨E.1,E.2.trans (by norm_num [cell12352])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy48 (n := 12352) (by norm_num)
        (q := 1 - (cell12352 ⟨48,by decide⟩).lower)
        (by norm_num [cell12352]) (by norm_num [cell12352])
      exact ⟨E.1,E.2.trans (by norm_num [cell12352])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy49 (n := 12352) (by norm_num)
        (q := 1 - (cell12352 ⟨49,by decide⟩).lower)
        (by norm_num [cell12352]) (by norm_num [cell12352])
      exact ⟨E.1,E.2.trans (by norm_num [cell12352])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy50 (n := 12352) (by norm_num)
        (q := 1 - (cell12352 ⟨50,by decide⟩).lower)
        (by norm_num [cell12352]) (by norm_num [cell12352])
      exact ⟨E.1,E.2.trans (by norm_num [cell12352])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy51 (n := 12352) (by norm_num)
        (q := 1 - (cell12352 ⟨51,by decide⟩).lower)
        (by norm_num [cell12352]) (by norm_num [cell12352])
      exact ⟨E.1,E.2.trans (by norm_num [cell12352])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy52 (n := 12352) (by norm_num)
        (q := 1 - (cell12352 ⟨52,by decide⟩).lower)
        (by norm_num [cell12352]) (by norm_num [cell12352])
      exact ⟨E.1,E.2.trans (by norm_num [cell12352])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12352

/-! Source-cell containment and simple scalar guards at 12352. -/
namespace BstLean.Part269.N12352
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12352)
open BstLean.Part268 (cell12352)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12352 ⟨10,by decide⟩).lower ∧ (cell12352 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12352 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12352 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12352 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12352 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12352 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12352,cell12352,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12352 ⟨11,by decide⟩).lower ∧ (cell12352 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12352 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12352 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12352 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12352 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12352 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12352,cell12352,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12352 ⟨12,by decide⟩).lower ∧ (cell12352 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12352 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12352 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12352 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12352 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12352 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12352,cell12352,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12352 ⟨13,by decide⟩).lower ∧ (cell12352 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12352 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12352 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12352 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12352 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12352 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12352,cell12352,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12352 ⟨14,by decide⟩).lower ∧ (cell12352 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12352 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12352 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12352 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12352 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12352 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12352,cell12352,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12352 ⟨15,by decide⟩).lower ∧ (cell12352 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12352 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12352 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12352 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12352 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12352 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12352,cell12352,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12352 ⟨16,by decide⟩).lower ∧ (cell12352 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12352 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12352 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12352 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12352 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12352 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12352,cell12352,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12352 ⟨17,by decide⟩).lower ∧ (cell12352 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12352 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12352 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12352 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12352 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12352 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12352,cell12352,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12352 ⟨18,by decide⟩).lower ∧ (cell12352 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12352 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12352 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12352 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12352 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12352 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12352,cell12352,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12352 ⟨19,by decide⟩).lower ∧ (cell12352 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12352 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12352 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12352 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12352 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12352 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12352,cell12352,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12352 ⟨20,by decide⟩).lower ∧ (cell12352 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12352 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12352 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12352 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12352 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12352 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12352,cell12352,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12352 ⟨21,by decide⟩).lower ∧ (cell12352 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12352 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12352 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12352 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12352 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12352 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12352,cell12352,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12352 ⟨22,by decide⟩).lower ∧ (cell12352 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12352 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12352 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12352 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12352 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12352 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12352,cell12352,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12352 ⟨23,by decide⟩).lower ∧ (cell12352 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12352 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12352 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12352 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12352 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12352 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12352,cell12352,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12352 ⟨24,by decide⟩).lower ∧ (cell12352 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12352 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12352 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12352 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12352 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12352 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12352,cell12352,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12352 ⟨25,by decide⟩).lower ∧ (cell12352 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12352 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12352 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12352 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12352 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12352 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12352,cell12352,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12352 ⟨26,by decide⟩).lower ∧ (cell12352 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12352 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12352 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12352 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12352 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12352 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12352,cell12352,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12352 ⟨27,by decide⟩).lower ∧ (cell12352 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12352 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12352 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12352 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12352 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12352 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12352,cell12352,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12352 ⟨28,by decide⟩).lower ∧ (cell12352 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12352 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12352 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12352 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12352 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12352 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12352,cell12352,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12352 ⟨29,by decide⟩).lower ∧ (cell12352 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12352 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12352 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12352 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12352 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12352 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12352,cell12352,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12352 ⟨30,by decide⟩).lower ∧ (cell12352 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12352 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12352 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12352 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12352 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12352 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12352,cell12352,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12352 ⟨31,by decide⟩).lower ∧ (cell12352 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12352 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12352 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12352 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12352 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12352 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12352,cell12352,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12352 ⟨32,by decide⟩).lower ∧ (cell12352 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12352 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12352 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12352 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12352 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12352 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12352,cell12352,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12352 ⟨33,by decide⟩).lower ∧ (cell12352 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12352 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12352 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12352 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12352 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12352 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12352,cell12352,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12352 ⟨34,by decide⟩).lower ∧ (cell12352 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12352 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12352 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12352 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12352 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12352 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12352,cell12352,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12352 ⟨35,by decide⟩).lower ∧ (cell12352 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12352 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12352 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12352 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12352 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12352 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12352,cell12352,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12352 ⟨36,by decide⟩).lower ∧ (cell12352 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12352 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12352 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12352 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12352 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12352 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12352,cell12352,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12352 ⟨37,by decide⟩).lower ∧ (cell12352 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12352 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12352 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12352 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12352 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12352 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12352,cell12352,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12352 ⟨38,by decide⟩).lower ∧ (cell12352 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12352 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12352 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12352 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12352 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12352 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12352,cell12352,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12352 ⟨39,by decide⟩).lower ∧ (cell12352 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12352 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12352 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12352 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12352 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12352 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12352,cell12352,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12352 ⟨40,by decide⟩).lower ∧ (cell12352 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12352 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12352 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12352 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12352 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12352 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12352,cell12352,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12352 ⟨41,by decide⟩).lower ∧ (cell12352 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12352 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12352 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12352 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12352 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12352 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12352,cell12352,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12352 ⟨42,by decide⟩).lower ∧ (cell12352 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12352 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12352 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12352 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12352 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12352 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12352,cell12352,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12352 ⟨43,by decide⟩).lower ∧ (cell12352 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12352 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12352 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12352 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12352 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12352 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12352,cell12352,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12352 ⟨44,by decide⟩).lower ∧ (cell12352 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12352 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12352 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12352 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12352 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12352 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12352,cell12352,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12352 ⟨45,by decide⟩).lower ∧ (cell12352 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12352 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12352 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12352 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12352 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12352 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12352,cell12352,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12352 ⟨46,by decide⟩).lower ∧ (cell12352 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12352 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12352 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12352 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12352 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12352 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12352,cell12352,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12352 ⟨47,by decide⟩).lower ∧ (cell12352 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12352 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12352 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12352 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12352 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12352 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12352,cell12352,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12352 ⟨48,by decide⟩).lower ∧ (cell12352 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12352 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12352 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12352 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12352 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12352 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12352,cell12352,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12352 ⟨49,by decide⟩).lower ∧ (cell12352 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12352 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12352 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12352 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12352 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12352 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12352,cell12352,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12352 ⟨50,by decide⟩).lower ∧ (cell12352 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12352 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12352 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12352 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12352 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12352 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12352,cell12352,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12352 ⟨51,by decide⟩).lower ∧ (cell12352 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12352 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12352 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12352 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12352 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12352 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12352,cell12352,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12352 ⟨52,by decide⟩).lower ∧ (cell12352 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12352 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12352 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12352 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12352 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12352 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12352,cell12352,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12352 i).lower ∧
    (cell12352 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12352 i).upper ≤ (0.532 : ℝ) ∧
    (cell12352 i).centre ≤ (0.1 : ℝ) ∧ (cell12352 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12352 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12352 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12352

/-! The local source numeric instances at 12352 have no network premises. -/
namespace BstLean.Part269.N12352
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12352)
open BstLean.Part268 (cell12352)

noncomputable def sourceNumerics12352 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12352 (cell12352 i)
      scalarRow12352.M scalarRow12352.H scalarRow12352.xi := by
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
    energy_allowance := scalarRow12352.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12352]
    centre_nonneg := (scalarRow12352.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D0.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12352])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12352
/-! Actual 12353 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12353
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12353 ≤ (1.036313138727 : ℝ) := by
  have hr : (111.144050672989 : ℝ) ≤ √(12353 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.144050672989 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12353 12353 (11 / 1000) ≤
    (0.008600434540 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12353) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.144050672989 : ℝ) ≤ √(12353 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12353)
  have hdiv : K / √(12353 : ℝ) ≤ K / 111.144050672989 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.144050672989 ≤ (0.008600434540 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12353.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12353 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12353 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12353 := gPlus_lower 12353
end BstLean.Part269.N12353

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12353
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036313138726 : ℝ) ≤ wn 12353 := by
  have hn : √(12353 : ℝ) ≤ 111.144050672990 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12353 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.144050672990 ≤ 2 / √(12353 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000259082270 : ℝ) ≤ rhoBar 12353 BstLean.Part154.csC ∧
    rhoBar 12353 BstLean.Part154.csC ≤ 0.000259082671 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036313138726 : ℝ) / (1.295212 * 12353) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036313138727 : ℝ) / (1.29521 * 12353) := by gcongr
      _ ≤ (0.000259082671 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12353 BstLean.Part154.csC) ≤ 0.001036397808 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12353 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12353 BstLean.Part154.csC) (piBar (rhoBar 12353 BstLean.Part154.csC)) ≤ 0.000197889355 ∧
    cc1 (rhoBar 12353 BstLean.Part154.csC) (piBar (rhoBar 12353 BstLean.Part154.csC)) ≤ 0.000125918256 ∧
    cc2 (rhoBar 12353 BstLean.Part154.csC) ≤ 0.000073096447 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12353 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12353 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12353 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12353 BstLean.Part154.csC * nuR (rhoBar 12353 BstLean.Part154.csC)) ≤ 0.000518182123 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000259082671 : ℝ) * 0.001036397808 := by gcongr
      _ ≤ (0.000518182123 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12353 BstLean.Part154.csC) * nuR (rhoBar 12353 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001036397808 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12353 BstLean.Part154.csC) * rhoBar 12353 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000259082671 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000259082671 / 2 + 0.399 * 0.001036397808 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000197889355 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000518182123 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125918256 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000259082671 / 1.414213562 := by gcongr
      _ ≤ (0.000073096447 : ℝ) := by norm_num

end BstLean.Part269.N12353

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12353
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12353 BstLean.Part154.csC) (piBar (rhoBar 12353 BstLean.Part154.csC)) ≤ 1.69114E-7 := by
  have hr0 : 0 ≤ rhoBar 12353 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12353 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12353 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12353 BstLean.Part154.csC) (piBar (rhoBar 12353 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12353 BstLean.Part154.csC) (piBar (rhoBar 12353 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12353 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000197889355 : ℝ) ^ 2 + 0.000125918256 ^ 2 + 3 * 0.000073096447 ^ 2 +
        2 * 0.797885 * 0.000197889355 * 0.000125918256 + 2 * 0.000197889355 * 0.000073096447 +
        4 * 0.797885 * 0.000125918256 * 0.000073096447 := by gcongr
    _ ≤ (1.69114E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12353 BstLean.Part154.csC Θ ≤ 0.002705782378 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12353 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12353 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12353 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12353 BstLean.Part154.csC) (piBar (rhoBar 12353 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12353 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036313138727 * 1.69114E-7 / (0.000259082270 : ℝ) := by gcongr
    _ ≤ 0.002705782378 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12353 BstLean.Part154.csC Θ ≤ 0.003003671994 + 0.000683706289 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12353 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12353 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12353 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036313138727 : ℝ) * ((2 * Θ * 0.000259082671 +
        (6863 / 10000) * 0.000259082671 * 12353 * 0.001036397808) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003003671994 + 0.000683706289 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12353 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12353 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12353 0.011 Θ ∧ gammaRatio 12353 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12353 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036313138727 : ℝ) * 0.525 / ((1 - 0.011) * 12353) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12353 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12353 0.011 Θ) :=
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
    badAllowance 12353 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12353 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12353 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12353 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12353 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12353 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12353 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12353 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12353 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12353 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12353 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036313138727 : ℝ) * 12353 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12353 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004103671994 + 0.003389488667 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12353

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12353
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12353 BstLean.Part154.csC) (piBar (rhoBar 12353 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12353 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12353 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12353 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12353 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12353 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12353 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12353 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12353 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12353 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12353 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12353 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12353 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12353 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12353 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053224407338 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12353) ≤ 0.010744952824 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12353 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036313138727)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010744952824 + 2 * 0.737676 / 12353) := by gcongr
    _ ≤ (0.053224407338 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12353 12 ≤ 0.0015 := by
  exact BstLean.Part269.S0.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12353

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12353
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560487435116 : ℝ) ≤ plow 12353 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12353) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053389753545)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001420535749) : eMP 12353 0.011 xi bn ≤ 0.001222507359 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12353 : ℝ) * (1 - 0.011))) ≤ 0.000604389176 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001420535749 / (12353 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000604389176 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000604389176 : ℝ) + 3.141593 * 0.053389753545 / (12353 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001222507359 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053389753545)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001420535749) : PiBarMP 12353 12 0.011 xi bn ≤ 0.163525007722 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12353 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037689995344 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.531068030667 : ℝ) ≤ √((12353 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.144050672989 : ℝ) ≤ √(12353 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12353) ≤ 0.125354512261 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037689995344 + 0.053389753545 * 1.772454 / (2 * (110.531068030667 : ℝ))) * (1 + 0.001222507359) +
        8 / (12353 * 111.144050672989) + 0.125354512261 := by gcongr
    _ ≤ (0.163525007722 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053389753545)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001420535749) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284286636067) :
    parallelOracle 12353 0.011 xi bn cd ≤ 0.164546816735 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12353 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12353 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560487435116 : ℝ) ≤ plow 12353 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.144050672989 : ℝ) ≤ √(12353 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284286636067 : ℝ) / (2 * 0.560487435116 * 111.144050672989)) * 0.163525007722 +
        0.284286636067 ^ 2 / (2 * 0.560487435116 * 111.144050672989) := by gcongr
    _ ≤ (0.164546816735 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053389753545) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001420535749)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284286636067) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12353 12353 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560487435116 : ℝ) ≤ plow 12353 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.144050672989 : ℝ) ≤ √(12353 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12353 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12353 Θ 1.22 ≤ 0.011931367374 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.144050672989 := by gcongr <;> linarith
      _ ≤ (0.011931367374 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12353 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12353 12353 0.011 ≤ 0.008600434540 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12353 12353 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12353 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12353 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12353 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12353 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164546816735 + 0.011931367374 + (0.008600434540 : ℝ) *
        (1 + 2 * (0.284286636067 + 0.011931367374) / (0.560487435116 * 111.144050672989))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12353]

end BstLean.Part269.N12353

/-! The original eight local profiles supply actual 12353 moment certificates. -/
namespace BstLean.Part269.N12353
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12353 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12353 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12353 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053389753545 ∧
    0 ≤ bN 12353 BstLean.Part154.csC (groupTheta g) ∧ bN 12353 BstLean.Part154.csC (groupTheta g) ≤ 0.001420535749 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12353 12353 0.011
      (momentAllowance 12353 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12353 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12353 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12353 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12353 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12353 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231062228729 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12353 0.011
      (momentAllowance 12353 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12353 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12353
/-! The actual computed-centre upper energy formula at 12353. -/
namespace BstLean.Part269.N12353
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12353

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12353
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12353)
open BstLean.Part268 (cell12353)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086576055962
  | 2 => 0.087540529479
  | 3 => 0.088506588756
  | 4 => 0.089476423364
  | 5 => 0.090452652343
  | 6 => 0.091438384044
  | 7 => 0.092437280906
  | 8 => 0.093453629088
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12353 12353 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12353 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004104440387 + 0.003390347157 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S0.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12353

/-! Actual upper energy certificates on all 43 source endpoints at 12353. -/
namespace BstLean.Part269.N12353
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12353)
open BstLean.Part268 (cell12353)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12353 (gMinus 12353) (1 - (cell12353 i).lower) ≤ 1 ∧
    energyUpper 12353 (gMinus 12353) (BstLean.Part211.gPlus 12353)
      (finiteEnergy 12353 12353 0.011) (1 - (cell12353 i).lower) ≤
      (cell12353 i).energy := by
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
      have E := BstLean.Part269.S0.uniformEnergy10 (n := 12353) (by norm_num)
        (q := 1 - (cell12353 ⟨10,by decide⟩).lower)
        (by norm_num [cell12353]) (by norm_num [cell12353])
      exact ⟨E.1,E.2.trans (by norm_num [cell12353])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy11 (n := 12353) (by norm_num)
        (q := 1 - (cell12353 ⟨11,by decide⟩).lower)
        (by norm_num [cell12353]) (by norm_num [cell12353])
      exact ⟨E.1,E.2.trans (by norm_num [cell12353])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy12 (n := 12353) (by norm_num)
        (q := 1 - (cell12353 ⟨12,by decide⟩).lower)
        (by norm_num [cell12353]) (by norm_num [cell12353])
      exact ⟨E.1,E.2.trans (by norm_num [cell12353])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy13 (n := 12353) (by norm_num)
        (q := 1 - (cell12353 ⟨13,by decide⟩).lower)
        (by norm_num [cell12353]) (by norm_num [cell12353])
      exact ⟨E.1,E.2.trans (by norm_num [cell12353])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy14 (n := 12353) (by norm_num)
        (q := 1 - (cell12353 ⟨14,by decide⟩).lower)
        (by norm_num [cell12353]) (by norm_num [cell12353])
      exact ⟨E.1,E.2.trans (by norm_num [cell12353])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy15 (n := 12353) (by norm_num)
        (q := 1 - (cell12353 ⟨15,by decide⟩).lower)
        (by norm_num [cell12353]) (by norm_num [cell12353])
      exact ⟨E.1,E.2.trans (by norm_num [cell12353])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy16 (n := 12353) (by norm_num)
        (q := 1 - (cell12353 ⟨16,by decide⟩).lower)
        (by norm_num [cell12353]) (by norm_num [cell12353])
      exact ⟨E.1,E.2.trans (by norm_num [cell12353])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy17 (n := 12353) (by norm_num)
        (q := 1 - (cell12353 ⟨17,by decide⟩).lower)
        (by norm_num [cell12353]) (by norm_num [cell12353])
      exact ⟨E.1,E.2.trans (by norm_num [cell12353])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy18 (n := 12353) (by norm_num)
        (q := 1 - (cell12353 ⟨18,by decide⟩).lower)
        (by norm_num [cell12353]) (by norm_num [cell12353])
      exact ⟨E.1,E.2.trans (by norm_num [cell12353])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy19 (n := 12353) (by norm_num)
        (q := 1 - (cell12353 ⟨19,by decide⟩).lower)
        (by norm_num [cell12353]) (by norm_num [cell12353])
      exact ⟨E.1,E.2.trans (by norm_num [cell12353])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy20 (n := 12353) (by norm_num)
        (q := 1 - (cell12353 ⟨20,by decide⟩).lower)
        (by norm_num [cell12353]) (by norm_num [cell12353])
      exact ⟨E.1,E.2.trans (by norm_num [cell12353])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy21 (n := 12353) (by norm_num)
        (q := 1 - (cell12353 ⟨21,by decide⟩).lower)
        (by norm_num [cell12353]) (by norm_num [cell12353])
      exact ⟨E.1,E.2.trans (by norm_num [cell12353])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy22 (n := 12353) (by norm_num)
        (q := 1 - (cell12353 ⟨22,by decide⟩).lower)
        (by norm_num [cell12353]) (by norm_num [cell12353])
      exact ⟨E.1,E.2.trans (by norm_num [cell12353])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy23 (n := 12353) (by norm_num)
        (q := 1 - (cell12353 ⟨23,by decide⟩).lower)
        (by norm_num [cell12353]) (by norm_num [cell12353])
      exact ⟨E.1,E.2.trans (by norm_num [cell12353])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy24 (n := 12353) (by norm_num)
        (q := 1 - (cell12353 ⟨24,by decide⟩).lower)
        (by norm_num [cell12353]) (by norm_num [cell12353])
      exact ⟨E.1,E.2.trans (by norm_num [cell12353])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy25 (n := 12353) (by norm_num)
        (q := 1 - (cell12353 ⟨25,by decide⟩).lower)
        (by norm_num [cell12353]) (by norm_num [cell12353])
      exact ⟨E.1,E.2.trans (by norm_num [cell12353])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy26 (n := 12353) (by norm_num)
        (q := 1 - (cell12353 ⟨26,by decide⟩).lower)
        (by norm_num [cell12353]) (by norm_num [cell12353])
      exact ⟨E.1,E.2.trans (by norm_num [cell12353])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy27 (n := 12353) (by norm_num)
        (q := 1 - (cell12353 ⟨27,by decide⟩).lower)
        (by norm_num [cell12353]) (by norm_num [cell12353])
      exact ⟨E.1,E.2.trans (by norm_num [cell12353])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy28 (n := 12353) (by norm_num)
        (q := 1 - (cell12353 ⟨28,by decide⟩).lower)
        (by norm_num [cell12353]) (by norm_num [cell12353])
      exact ⟨E.1,E.2.trans (by norm_num [cell12353])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy29 (n := 12353) (by norm_num)
        (q := 1 - (cell12353 ⟨29,by decide⟩).lower)
        (by norm_num [cell12353]) (by norm_num [cell12353])
      exact ⟨E.1,E.2.trans (by norm_num [cell12353])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy30 (n := 12353) (by norm_num)
        (q := 1 - (cell12353 ⟨30,by decide⟩).lower)
        (by norm_num [cell12353]) (by norm_num [cell12353])
      exact ⟨E.1,E.2.trans (by norm_num [cell12353])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy31 (n := 12353) (by norm_num)
        (q := 1 - (cell12353 ⟨31,by decide⟩).lower)
        (by norm_num [cell12353]) (by norm_num [cell12353])
      exact ⟨E.1,E.2.trans (by norm_num [cell12353])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy32 (n := 12353) (by norm_num)
        (q := 1 - (cell12353 ⟨32,by decide⟩).lower)
        (by norm_num [cell12353]) (by norm_num [cell12353])
      exact ⟨E.1,E.2.trans (by norm_num [cell12353])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy33 (n := 12353) (by norm_num)
        (q := 1 - (cell12353 ⟨33,by decide⟩).lower)
        (by norm_num [cell12353]) (by norm_num [cell12353])
      exact ⟨E.1,E.2.trans (by norm_num [cell12353])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy34 (n := 12353) (by norm_num)
        (q := 1 - (cell12353 ⟨34,by decide⟩).lower)
        (by norm_num [cell12353]) (by norm_num [cell12353])
      exact ⟨E.1,E.2.trans (by norm_num [cell12353])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy35 (n := 12353) (by norm_num)
        (q := 1 - (cell12353 ⟨35,by decide⟩).lower)
        (by norm_num [cell12353]) (by norm_num [cell12353])
      exact ⟨E.1,E.2.trans (by norm_num [cell12353])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy36 (n := 12353) (by norm_num)
        (q := 1 - (cell12353 ⟨36,by decide⟩).lower)
        (by norm_num [cell12353]) (by norm_num [cell12353])
      exact ⟨E.1,E.2.trans (by norm_num [cell12353])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy37 (n := 12353) (by norm_num)
        (q := 1 - (cell12353 ⟨37,by decide⟩).lower)
        (by norm_num [cell12353]) (by norm_num [cell12353])
      exact ⟨E.1,E.2.trans (by norm_num [cell12353])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy38 (n := 12353) (by norm_num)
        (q := 1 - (cell12353 ⟨38,by decide⟩).lower)
        (by norm_num [cell12353]) (by norm_num [cell12353])
      exact ⟨E.1,E.2.trans (by norm_num [cell12353])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy39 (n := 12353) (by norm_num)
        (q := 1 - (cell12353 ⟨39,by decide⟩).lower)
        (by norm_num [cell12353]) (by norm_num [cell12353])
      exact ⟨E.1,E.2.trans (by norm_num [cell12353])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy40 (n := 12353) (by norm_num)
        (q := 1 - (cell12353 ⟨40,by decide⟩).lower)
        (by norm_num [cell12353]) (by norm_num [cell12353])
      exact ⟨E.1,E.2.trans (by norm_num [cell12353])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy41 (n := 12353) (by norm_num)
        (q := 1 - (cell12353 ⟨41,by decide⟩).lower)
        (by norm_num [cell12353]) (by norm_num [cell12353])
      exact ⟨E.1,E.2.trans (by norm_num [cell12353])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy42 (n := 12353) (by norm_num)
        (q := 1 - (cell12353 ⟨42,by decide⟩).lower)
        (by norm_num [cell12353]) (by norm_num [cell12353])
      exact ⟨E.1,E.2.trans (by norm_num [cell12353])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy43 (n := 12353) (by norm_num)
        (q := 1 - (cell12353 ⟨43,by decide⟩).lower)
        (by norm_num [cell12353]) (by norm_num [cell12353])
      exact ⟨E.1,E.2.trans (by norm_num [cell12353])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy44 (n := 12353) (by norm_num)
        (q := 1 - (cell12353 ⟨44,by decide⟩).lower)
        (by norm_num [cell12353]) (by norm_num [cell12353])
      exact ⟨E.1,E.2.trans (by norm_num [cell12353])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy45 (n := 12353) (by norm_num)
        (q := 1 - (cell12353 ⟨45,by decide⟩).lower)
        (by norm_num [cell12353]) (by norm_num [cell12353])
      exact ⟨E.1,E.2.trans (by norm_num [cell12353])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy46 (n := 12353) (by norm_num)
        (q := 1 - (cell12353 ⟨46,by decide⟩).lower)
        (by norm_num [cell12353]) (by norm_num [cell12353])
      exact ⟨E.1,E.2.trans (by norm_num [cell12353])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy47 (n := 12353) (by norm_num)
        (q := 1 - (cell12353 ⟨47,by decide⟩).lower)
        (by norm_num [cell12353]) (by norm_num [cell12353])
      exact ⟨E.1,E.2.trans (by norm_num [cell12353])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy48 (n := 12353) (by norm_num)
        (q := 1 - (cell12353 ⟨48,by decide⟩).lower)
        (by norm_num [cell12353]) (by norm_num [cell12353])
      exact ⟨E.1,E.2.trans (by norm_num [cell12353])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy49 (n := 12353) (by norm_num)
        (q := 1 - (cell12353 ⟨49,by decide⟩).lower)
        (by norm_num [cell12353]) (by norm_num [cell12353])
      exact ⟨E.1,E.2.trans (by norm_num [cell12353])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy50 (n := 12353) (by norm_num)
        (q := 1 - (cell12353 ⟨50,by decide⟩).lower)
        (by norm_num [cell12353]) (by norm_num [cell12353])
      exact ⟨E.1,E.2.trans (by norm_num [cell12353])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy51 (n := 12353) (by norm_num)
        (q := 1 - (cell12353 ⟨51,by decide⟩).lower)
        (by norm_num [cell12353]) (by norm_num [cell12353])
      exact ⟨E.1,E.2.trans (by norm_num [cell12353])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy52 (n := 12353) (by norm_num)
        (q := 1 - (cell12353 ⟨52,by decide⟩).lower)
        (by norm_num [cell12353]) (by norm_num [cell12353])
      exact ⟨E.1,E.2.trans (by norm_num [cell12353])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12353

/-! Source-cell containment and simple scalar guards at 12353. -/
namespace BstLean.Part269.N12353
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12353)
open BstLean.Part268 (cell12353)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12353 ⟨10,by decide⟩).lower ∧ (cell12353 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12353 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12353 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12353 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12353 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12353 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12353,cell12353,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12353 ⟨11,by decide⟩).lower ∧ (cell12353 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12353 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12353 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12353 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12353 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12353 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12353,cell12353,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12353 ⟨12,by decide⟩).lower ∧ (cell12353 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12353 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12353 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12353 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12353 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12353 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12353,cell12353,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12353 ⟨13,by decide⟩).lower ∧ (cell12353 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12353 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12353 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12353 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12353 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12353 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12353,cell12353,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12353 ⟨14,by decide⟩).lower ∧ (cell12353 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12353 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12353 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12353 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12353 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12353 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12353,cell12353,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12353 ⟨15,by decide⟩).lower ∧ (cell12353 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12353 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12353 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12353 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12353 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12353 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12353,cell12353,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12353 ⟨16,by decide⟩).lower ∧ (cell12353 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12353 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12353 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12353 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12353 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12353 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12353,cell12353,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12353 ⟨17,by decide⟩).lower ∧ (cell12353 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12353 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12353 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12353 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12353 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12353 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12353,cell12353,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12353 ⟨18,by decide⟩).lower ∧ (cell12353 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12353 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12353 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12353 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12353 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12353 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12353,cell12353,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12353 ⟨19,by decide⟩).lower ∧ (cell12353 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12353 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12353 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12353 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12353 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12353 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12353,cell12353,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12353 ⟨20,by decide⟩).lower ∧ (cell12353 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12353 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12353 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12353 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12353 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12353 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12353,cell12353,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12353 ⟨21,by decide⟩).lower ∧ (cell12353 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12353 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12353 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12353 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12353 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12353 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12353,cell12353,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12353 ⟨22,by decide⟩).lower ∧ (cell12353 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12353 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12353 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12353 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12353 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12353 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12353,cell12353,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12353 ⟨23,by decide⟩).lower ∧ (cell12353 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12353 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12353 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12353 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12353 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12353 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12353,cell12353,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12353 ⟨24,by decide⟩).lower ∧ (cell12353 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12353 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12353 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12353 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12353 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12353 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12353,cell12353,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12353 ⟨25,by decide⟩).lower ∧ (cell12353 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12353 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12353 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12353 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12353 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12353 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12353,cell12353,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12353 ⟨26,by decide⟩).lower ∧ (cell12353 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12353 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12353 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12353 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12353 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12353 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12353,cell12353,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12353 ⟨27,by decide⟩).lower ∧ (cell12353 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12353 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12353 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12353 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12353 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12353 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12353,cell12353,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12353 ⟨28,by decide⟩).lower ∧ (cell12353 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12353 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12353 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12353 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12353 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12353 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12353,cell12353,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12353 ⟨29,by decide⟩).lower ∧ (cell12353 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12353 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12353 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12353 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12353 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12353 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12353,cell12353,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12353 ⟨30,by decide⟩).lower ∧ (cell12353 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12353 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12353 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12353 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12353 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12353 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12353,cell12353,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12353 ⟨31,by decide⟩).lower ∧ (cell12353 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12353 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12353 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12353 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12353 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12353 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12353,cell12353,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12353 ⟨32,by decide⟩).lower ∧ (cell12353 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12353 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12353 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12353 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12353 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12353 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12353,cell12353,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12353 ⟨33,by decide⟩).lower ∧ (cell12353 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12353 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12353 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12353 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12353 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12353 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12353,cell12353,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12353 ⟨34,by decide⟩).lower ∧ (cell12353 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12353 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12353 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12353 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12353 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12353 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12353,cell12353,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12353 ⟨35,by decide⟩).lower ∧ (cell12353 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12353 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12353 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12353 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12353 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12353 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12353,cell12353,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12353 ⟨36,by decide⟩).lower ∧ (cell12353 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12353 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12353 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12353 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12353 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12353 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12353,cell12353,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12353 ⟨37,by decide⟩).lower ∧ (cell12353 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12353 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12353 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12353 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12353 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12353 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12353,cell12353,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12353 ⟨38,by decide⟩).lower ∧ (cell12353 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12353 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12353 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12353 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12353 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12353 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12353,cell12353,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12353 ⟨39,by decide⟩).lower ∧ (cell12353 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12353 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12353 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12353 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12353 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12353 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12353,cell12353,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12353 ⟨40,by decide⟩).lower ∧ (cell12353 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12353 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12353 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12353 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12353 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12353 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12353,cell12353,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12353 ⟨41,by decide⟩).lower ∧ (cell12353 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12353 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12353 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12353 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12353 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12353 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12353,cell12353,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12353 ⟨42,by decide⟩).lower ∧ (cell12353 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12353 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12353 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12353 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12353 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12353 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12353,cell12353,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12353 ⟨43,by decide⟩).lower ∧ (cell12353 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12353 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12353 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12353 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12353 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12353 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12353,cell12353,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12353 ⟨44,by decide⟩).lower ∧ (cell12353 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12353 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12353 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12353 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12353 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12353 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12353,cell12353,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12353 ⟨45,by decide⟩).lower ∧ (cell12353 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12353 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12353 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12353 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12353 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12353 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12353,cell12353,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12353 ⟨46,by decide⟩).lower ∧ (cell12353 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12353 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12353 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12353 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12353 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12353 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12353,cell12353,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12353 ⟨47,by decide⟩).lower ∧ (cell12353 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12353 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12353 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12353 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12353 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12353 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12353,cell12353,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12353 ⟨48,by decide⟩).lower ∧ (cell12353 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12353 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12353 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12353 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12353 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12353 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12353,cell12353,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12353 ⟨49,by decide⟩).lower ∧ (cell12353 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12353 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12353 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12353 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12353 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12353 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12353,cell12353,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12353 ⟨50,by decide⟩).lower ∧ (cell12353 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12353 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12353 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12353 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12353 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12353 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12353,cell12353,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12353 ⟨51,by decide⟩).lower ∧ (cell12353 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12353 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12353 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12353 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12353 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12353 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12353,cell12353,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12353 ⟨52,by decide⟩).lower ∧ (cell12353 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12353 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12353 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12353 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12353 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12353 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12353,cell12353,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12353 i).lower ∧
    (cell12353 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12353 i).upper ≤ (0.532 : ℝ) ∧
    (cell12353 i).centre ≤ (0.1 : ℝ) ∧ (cell12353 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12353 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12353 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12353

/-! The local source numeric instances at 12353 have no network premises. -/
namespace BstLean.Part269.N12353
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12353)
open BstLean.Part268 (cell12353)

noncomputable def sourceNumerics12353 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12353 (cell12353 i)
      scalarRow12353.M scalarRow12353.H scalarRow12353.xi := by
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
    energy_allowance := scalarRow12353.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12353]
    centre_nonneg := (scalarRow12353.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D0.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12353])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12353
/-! Actual 12354 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12354
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12354 ≤ (1.036311655901 : ℝ) := by
  have hr : (111.148549248292 : ℝ) ≤ √(12354 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.148549248292 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12354 12354 (11 / 1000) ≤
    (0.008600086447 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12354) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.148549248292 : ℝ) ≤ √(12354 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12354)
  have hdiv : K / √(12354 : ℝ) ≤ K / 111.148549248292 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.148549248292 ≤ (0.008600086447 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12354.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12354 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12354 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12354 := gPlus_lower 12354
end BstLean.Part269.N12354

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12354
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036311655900 : ℝ) ≤ wn 12354 := by
  have hn : √(12354 : ℝ) ≤ 111.148549248293 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12354 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.148549248293 ≤ 2 / √(12354 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000259060928 : ℝ) ≤ rhoBar 12354 BstLean.Part154.csC ∧
    rhoBar 12354 BstLean.Part154.csC ≤ 0.000259061329 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036311655900 : ℝ) / (1.295212 * 12354) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036311655901 : ℝ) / (1.29521 * 12354) := by gcongr
      _ ≤ (0.000259061329 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12354 BstLean.Part154.csC) ≤ 0.001036312429 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12354 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12354 BstLean.Part154.csC) (piBar (rhoBar 12354 BstLean.Part154.csC)) ≤ 0.000197873053 ∧
    cc1 (rhoBar 12354 BstLean.Part154.csC) (piBar (rhoBar 12354 BstLean.Part154.csC)) ≤ 0.000125907883 ∧
    cc2 (rhoBar 12354 BstLean.Part154.csC) ≤ 0.000073090425 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12354 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12354 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12354 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12354 BstLean.Part154.csC * nuR (rhoBar 12354 BstLean.Part154.csC)) ≤ 0.000518139436 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000259061329 : ℝ) * 0.001036312429 := by gcongr
      _ ≤ (0.000518139436 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12354 BstLean.Part154.csC) * nuR (rhoBar 12354 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001036312429 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12354 BstLean.Part154.csC) * rhoBar 12354 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000259061329 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000259061329 / 2 + 0.399 * 0.001036312429 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000197873053 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000518139436 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125907883 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000259061329 / 1.414213562 := by gcongr
      _ ≤ (0.000073090425 : ℝ) := by norm_num

end BstLean.Part269.N12354

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12354
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12354 BstLean.Part154.csC) (piBar (rhoBar 12354 BstLean.Part154.csC)) ≤ 1.69086E-7 := by
  have hr0 : 0 ≤ rhoBar 12354 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12354 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12354 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12354 BstLean.Part154.csC) (piBar (rhoBar 12354 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12354 BstLean.Part154.csC) (piBar (rhoBar 12354 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12354 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000197873053 : ℝ) ^ 2 + 0.000125907883 ^ 2 + 3 * 0.000073090425 ^ 2 +
        2 * 0.797885 * 0.000197873053 * 0.000125907883 + 2 * 0.000197873053 * 0.000073090425 +
        4 * 0.797885 * 0.000125907883 * 0.000073090425 := by gcongr
    _ ≤ (1.69086E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12354 BstLean.Part154.csC Θ ≤ 0.002705553385 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12354 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12354 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12354 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12354 BstLean.Part154.csC) (piBar (rhoBar 12354 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12354 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036311655901 * 1.69086E-7 / (0.000259060928 : ℝ) := by gcongr
    _ ≤ 0.002705553385 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12354 BstLean.Part154.csC Θ ≤ 0.003003415958 + 0.000683648991 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12354 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12354 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12354 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036311655901 : ℝ) * ((2 * Θ * 0.000259061329 +
        (6863 / 10000) * 0.000259061329 * 12354 * 0.001036312429) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003003415958 + 0.000683648991 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12354 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12354 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12354 0.011 Θ ∧ gammaRatio 12354 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12354 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036311655901 : ℝ) * 0.525 / ((1 - 0.011) * 12354) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12354 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12354 0.011 Θ) :=
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
    badAllowance 12354 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12354 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12354 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12354 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12354 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12354 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12354 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12354 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12354 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12354 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12354 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036311655901 : ℝ) * 12354 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12354 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004103415958 + 0.003389202376 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12354

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12354
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12354 BstLean.Part154.csC) (piBar (rhoBar 12354 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12354 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12354 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12354 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12354 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12354 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12354 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12354 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12354 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12354 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12354 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12354 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12354 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12354 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12354 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053222229474 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12354) ≤ 0.010744517937 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12354 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036311655901)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010744517937 + 2 * 0.737676 / 12354) := by gcongr
    _ ≤ (0.053222229474 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12354 12 ≤ 0.0015 := by
  exact BstLean.Part269.S0.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12354

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12354
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560487482912 : ℝ) ≤ plow 12354 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12354) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053389347206)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001420415528) : eMP 12354 0.011 xi bn ≤ 0.001222406071 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12354 : ℝ) * (1 - 0.011))) ≤ 0.000604339140 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001420415528 / (12354 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000604339140 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000604339140 : ℝ) + 3.141593 * 0.053389347206 / (12354 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001222406071 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053389347206)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001420415528) : PiBarMP 12354 12 0.011 xi bn ≤ 0.163518312155 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12354 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037688400444 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.535541795388 : ℝ) ≤ √((12354 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.148549248292 : ℝ) ≤ √(12354 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12354) ≤ 0.125349438720 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037688400444 + 0.053389347206 * 1.772454 / (2 * (110.535541795388 : ℝ))) * (1 + 0.001222406071) +
        8 / (12354 * 111.148549248292) + 0.125349438720 := by gcongr
    _ ≤ (0.163518312155 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053389347206)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001420415528) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284283578917) :
    parallelOracle 12354 0.011 xi bn cd ≤ 0.164540046484 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12354 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12354 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560487482912 : ℝ) ≤ plow 12354 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.148549248292 : ℝ) ≤ √(12354 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284283578917 : ℝ) / (2 * 0.560487482912 * 111.148549248292)) * 0.163518312155 +
        0.284283578917 ^ 2 / (2 * 0.560487482912 * 111.148549248292) := by gcongr
    _ ≤ (0.164540046484 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053389347206) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001420415528)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284283578917) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12354 12354 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560487482912 : ℝ) ≤ plow 12354 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.148549248292 : ℝ) ≤ √(12354 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12354 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12354 Θ 1.22 ≤ 0.011930884470 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.148549248292 := by gcongr <;> linarith
      _ ≤ (0.011930884470 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12354 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12354 12354 0.011 ≤ 0.008600086447 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12354 12354 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12354 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12354 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12354 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12354 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164540046484 + 0.011930884470 + (0.008600086447 : ℝ) *
        (1 + 2 * (0.284283578917 + 0.011930884470) / (0.560487482912 * 111.148549248292))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12354]

end BstLean.Part269.N12354

/-! The original eight local profiles supply actual 12354 moment certificates. -/
namespace BstLean.Part269.N12354
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12354 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12354 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12354 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053389347206 ∧
    0 ≤ bN 12354 BstLean.Part154.csC (groupTheta g) ∧ bN 12354 BstLean.Part154.csC (groupTheta g) ≤ 0.001420415528 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12354 12354 0.011
      (momentAllowance 12354 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12354 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12354 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12354 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12354 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12354 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231061349443 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12354 0.011
      (momentAllowance 12354 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12354 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12354
/-! The actual computed-centre upper energy formula at 12354. -/
namespace BstLean.Part269.N12354
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12354

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12354
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12354)
open BstLean.Part268 (cell12354)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086572687097
  | 2 => 0.087537087543
  | 3 => 0.088503061374
  | 4 => 0.089472795460
  | 5 => 0.090448905683
  | 6 => 0.091434496736
  | 7 => 0.092433226843
  | 8 => 0.093449377336
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12354 12354 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12354 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004104440387 + 0.003390347157 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S0.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12354

/-! Actual upper energy certificates on all 43 source endpoints at 12354. -/
namespace BstLean.Part269.N12354
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12354)
open BstLean.Part268 (cell12354)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12354 (gMinus 12354) (1 - (cell12354 i).lower) ≤ 1 ∧
    energyUpper 12354 (gMinus 12354) (BstLean.Part211.gPlus 12354)
      (finiteEnergy 12354 12354 0.011) (1 - (cell12354 i).lower) ≤
      (cell12354 i).energy := by
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
      have E := BstLean.Part269.S0.uniformEnergy10 (n := 12354) (by norm_num)
        (q := 1 - (cell12354 ⟨10,by decide⟩).lower)
        (by norm_num [cell12354]) (by norm_num [cell12354])
      exact ⟨E.1,E.2.trans (by norm_num [cell12354])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy11 (n := 12354) (by norm_num)
        (q := 1 - (cell12354 ⟨11,by decide⟩).lower)
        (by norm_num [cell12354]) (by norm_num [cell12354])
      exact ⟨E.1,E.2.trans (by norm_num [cell12354])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy12 (n := 12354) (by norm_num)
        (q := 1 - (cell12354 ⟨12,by decide⟩).lower)
        (by norm_num [cell12354]) (by norm_num [cell12354])
      exact ⟨E.1,E.2.trans (by norm_num [cell12354])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy13 (n := 12354) (by norm_num)
        (q := 1 - (cell12354 ⟨13,by decide⟩).lower)
        (by norm_num [cell12354]) (by norm_num [cell12354])
      exact ⟨E.1,E.2.trans (by norm_num [cell12354])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy14 (n := 12354) (by norm_num)
        (q := 1 - (cell12354 ⟨14,by decide⟩).lower)
        (by norm_num [cell12354]) (by norm_num [cell12354])
      exact ⟨E.1,E.2.trans (by norm_num [cell12354])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy15 (n := 12354) (by norm_num)
        (q := 1 - (cell12354 ⟨15,by decide⟩).lower)
        (by norm_num [cell12354]) (by norm_num [cell12354])
      exact ⟨E.1,E.2.trans (by norm_num [cell12354])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy16 (n := 12354) (by norm_num)
        (q := 1 - (cell12354 ⟨16,by decide⟩).lower)
        (by norm_num [cell12354]) (by norm_num [cell12354])
      exact ⟨E.1,E.2.trans (by norm_num [cell12354])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy17 (n := 12354) (by norm_num)
        (q := 1 - (cell12354 ⟨17,by decide⟩).lower)
        (by norm_num [cell12354]) (by norm_num [cell12354])
      exact ⟨E.1,E.2.trans (by norm_num [cell12354])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy18 (n := 12354) (by norm_num)
        (q := 1 - (cell12354 ⟨18,by decide⟩).lower)
        (by norm_num [cell12354]) (by norm_num [cell12354])
      exact ⟨E.1,E.2.trans (by norm_num [cell12354])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy19 (n := 12354) (by norm_num)
        (q := 1 - (cell12354 ⟨19,by decide⟩).lower)
        (by norm_num [cell12354]) (by norm_num [cell12354])
      exact ⟨E.1,E.2.trans (by norm_num [cell12354])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy20 (n := 12354) (by norm_num)
        (q := 1 - (cell12354 ⟨20,by decide⟩).lower)
        (by norm_num [cell12354]) (by norm_num [cell12354])
      exact ⟨E.1,E.2.trans (by norm_num [cell12354])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy21 (n := 12354) (by norm_num)
        (q := 1 - (cell12354 ⟨21,by decide⟩).lower)
        (by norm_num [cell12354]) (by norm_num [cell12354])
      exact ⟨E.1,E.2.trans (by norm_num [cell12354])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy22 (n := 12354) (by norm_num)
        (q := 1 - (cell12354 ⟨22,by decide⟩).lower)
        (by norm_num [cell12354]) (by norm_num [cell12354])
      exact ⟨E.1,E.2.trans (by norm_num [cell12354])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy23 (n := 12354) (by norm_num)
        (q := 1 - (cell12354 ⟨23,by decide⟩).lower)
        (by norm_num [cell12354]) (by norm_num [cell12354])
      exact ⟨E.1,E.2.trans (by norm_num [cell12354])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy24 (n := 12354) (by norm_num)
        (q := 1 - (cell12354 ⟨24,by decide⟩).lower)
        (by norm_num [cell12354]) (by norm_num [cell12354])
      exact ⟨E.1,E.2.trans (by norm_num [cell12354])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy25 (n := 12354) (by norm_num)
        (q := 1 - (cell12354 ⟨25,by decide⟩).lower)
        (by norm_num [cell12354]) (by norm_num [cell12354])
      exact ⟨E.1,E.2.trans (by norm_num [cell12354])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy26 (n := 12354) (by norm_num)
        (q := 1 - (cell12354 ⟨26,by decide⟩).lower)
        (by norm_num [cell12354]) (by norm_num [cell12354])
      exact ⟨E.1,E.2.trans (by norm_num [cell12354])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy27 (n := 12354) (by norm_num)
        (q := 1 - (cell12354 ⟨27,by decide⟩).lower)
        (by norm_num [cell12354]) (by norm_num [cell12354])
      exact ⟨E.1,E.2.trans (by norm_num [cell12354])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy28 (n := 12354) (by norm_num)
        (q := 1 - (cell12354 ⟨28,by decide⟩).lower)
        (by norm_num [cell12354]) (by norm_num [cell12354])
      exact ⟨E.1,E.2.trans (by norm_num [cell12354])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy29 (n := 12354) (by norm_num)
        (q := 1 - (cell12354 ⟨29,by decide⟩).lower)
        (by norm_num [cell12354]) (by norm_num [cell12354])
      exact ⟨E.1,E.2.trans (by norm_num [cell12354])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy30 (n := 12354) (by norm_num)
        (q := 1 - (cell12354 ⟨30,by decide⟩).lower)
        (by norm_num [cell12354]) (by norm_num [cell12354])
      exact ⟨E.1,E.2.trans (by norm_num [cell12354])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy31 (n := 12354) (by norm_num)
        (q := 1 - (cell12354 ⟨31,by decide⟩).lower)
        (by norm_num [cell12354]) (by norm_num [cell12354])
      exact ⟨E.1,E.2.trans (by norm_num [cell12354])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy32 (n := 12354) (by norm_num)
        (q := 1 - (cell12354 ⟨32,by decide⟩).lower)
        (by norm_num [cell12354]) (by norm_num [cell12354])
      exact ⟨E.1,E.2.trans (by norm_num [cell12354])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy33 (n := 12354) (by norm_num)
        (q := 1 - (cell12354 ⟨33,by decide⟩).lower)
        (by norm_num [cell12354]) (by norm_num [cell12354])
      exact ⟨E.1,E.2.trans (by norm_num [cell12354])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy34 (n := 12354) (by norm_num)
        (q := 1 - (cell12354 ⟨34,by decide⟩).lower)
        (by norm_num [cell12354]) (by norm_num [cell12354])
      exact ⟨E.1,E.2.trans (by norm_num [cell12354])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy35 (n := 12354) (by norm_num)
        (q := 1 - (cell12354 ⟨35,by decide⟩).lower)
        (by norm_num [cell12354]) (by norm_num [cell12354])
      exact ⟨E.1,E.2.trans (by norm_num [cell12354])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy36 (n := 12354) (by norm_num)
        (q := 1 - (cell12354 ⟨36,by decide⟩).lower)
        (by norm_num [cell12354]) (by norm_num [cell12354])
      exact ⟨E.1,E.2.trans (by norm_num [cell12354])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy37 (n := 12354) (by norm_num)
        (q := 1 - (cell12354 ⟨37,by decide⟩).lower)
        (by norm_num [cell12354]) (by norm_num [cell12354])
      exact ⟨E.1,E.2.trans (by norm_num [cell12354])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy38 (n := 12354) (by norm_num)
        (q := 1 - (cell12354 ⟨38,by decide⟩).lower)
        (by norm_num [cell12354]) (by norm_num [cell12354])
      exact ⟨E.1,E.2.trans (by norm_num [cell12354])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy39 (n := 12354) (by norm_num)
        (q := 1 - (cell12354 ⟨39,by decide⟩).lower)
        (by norm_num [cell12354]) (by norm_num [cell12354])
      exact ⟨E.1,E.2.trans (by norm_num [cell12354])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy40 (n := 12354) (by norm_num)
        (q := 1 - (cell12354 ⟨40,by decide⟩).lower)
        (by norm_num [cell12354]) (by norm_num [cell12354])
      exact ⟨E.1,E.2.trans (by norm_num [cell12354])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy41 (n := 12354) (by norm_num)
        (q := 1 - (cell12354 ⟨41,by decide⟩).lower)
        (by norm_num [cell12354]) (by norm_num [cell12354])
      exact ⟨E.1,E.2.trans (by norm_num [cell12354])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy42 (n := 12354) (by norm_num)
        (q := 1 - (cell12354 ⟨42,by decide⟩).lower)
        (by norm_num [cell12354]) (by norm_num [cell12354])
      exact ⟨E.1,E.2.trans (by norm_num [cell12354])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy43 (n := 12354) (by norm_num)
        (q := 1 - (cell12354 ⟨43,by decide⟩).lower)
        (by norm_num [cell12354]) (by norm_num [cell12354])
      exact ⟨E.1,E.2.trans (by norm_num [cell12354])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy44 (n := 12354) (by norm_num)
        (q := 1 - (cell12354 ⟨44,by decide⟩).lower)
        (by norm_num [cell12354]) (by norm_num [cell12354])
      exact ⟨E.1,E.2.trans (by norm_num [cell12354])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy45 (n := 12354) (by norm_num)
        (q := 1 - (cell12354 ⟨45,by decide⟩).lower)
        (by norm_num [cell12354]) (by norm_num [cell12354])
      exact ⟨E.1,E.2.trans (by norm_num [cell12354])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy46 (n := 12354) (by norm_num)
        (q := 1 - (cell12354 ⟨46,by decide⟩).lower)
        (by norm_num [cell12354]) (by norm_num [cell12354])
      exact ⟨E.1,E.2.trans (by norm_num [cell12354])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy47 (n := 12354) (by norm_num)
        (q := 1 - (cell12354 ⟨47,by decide⟩).lower)
        (by norm_num [cell12354]) (by norm_num [cell12354])
      exact ⟨E.1,E.2.trans (by norm_num [cell12354])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy48 (n := 12354) (by norm_num)
        (q := 1 - (cell12354 ⟨48,by decide⟩).lower)
        (by norm_num [cell12354]) (by norm_num [cell12354])
      exact ⟨E.1,E.2.trans (by norm_num [cell12354])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy49 (n := 12354) (by norm_num)
        (q := 1 - (cell12354 ⟨49,by decide⟩).lower)
        (by norm_num [cell12354]) (by norm_num [cell12354])
      exact ⟨E.1,E.2.trans (by norm_num [cell12354])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy50 (n := 12354) (by norm_num)
        (q := 1 - (cell12354 ⟨50,by decide⟩).lower)
        (by norm_num [cell12354]) (by norm_num [cell12354])
      exact ⟨E.1,E.2.trans (by norm_num [cell12354])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy51 (n := 12354) (by norm_num)
        (q := 1 - (cell12354 ⟨51,by decide⟩).lower)
        (by norm_num [cell12354]) (by norm_num [cell12354])
      exact ⟨E.1,E.2.trans (by norm_num [cell12354])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy52 (n := 12354) (by norm_num)
        (q := 1 - (cell12354 ⟨52,by decide⟩).lower)
        (by norm_num [cell12354]) (by norm_num [cell12354])
      exact ⟨E.1,E.2.trans (by norm_num [cell12354])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12354

/-! Source-cell containment and simple scalar guards at 12354. -/
namespace BstLean.Part269.N12354
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12354)
open BstLean.Part268 (cell12354)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12354 ⟨10,by decide⟩).lower ∧ (cell12354 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12354 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12354 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12354 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12354 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12354 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12354,cell12354,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12354 ⟨11,by decide⟩).lower ∧ (cell12354 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12354 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12354 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12354 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12354 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12354 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12354,cell12354,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12354 ⟨12,by decide⟩).lower ∧ (cell12354 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12354 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12354 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12354 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12354 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12354 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12354,cell12354,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12354 ⟨13,by decide⟩).lower ∧ (cell12354 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12354 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12354 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12354 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12354 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12354 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12354,cell12354,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12354 ⟨14,by decide⟩).lower ∧ (cell12354 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12354 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12354 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12354 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12354 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12354 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12354,cell12354,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12354 ⟨15,by decide⟩).lower ∧ (cell12354 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12354 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12354 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12354 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12354 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12354 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12354,cell12354,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12354 ⟨16,by decide⟩).lower ∧ (cell12354 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12354 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12354 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12354 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12354 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12354 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12354,cell12354,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12354 ⟨17,by decide⟩).lower ∧ (cell12354 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12354 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12354 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12354 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12354 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12354 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12354,cell12354,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12354 ⟨18,by decide⟩).lower ∧ (cell12354 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12354 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12354 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12354 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12354 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12354 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12354,cell12354,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12354 ⟨19,by decide⟩).lower ∧ (cell12354 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12354 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12354 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12354 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12354 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12354 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12354,cell12354,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12354 ⟨20,by decide⟩).lower ∧ (cell12354 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12354 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12354 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12354 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12354 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12354 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12354,cell12354,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12354 ⟨21,by decide⟩).lower ∧ (cell12354 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12354 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12354 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12354 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12354 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12354 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12354,cell12354,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12354 ⟨22,by decide⟩).lower ∧ (cell12354 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12354 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12354 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12354 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12354 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12354 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12354,cell12354,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12354 ⟨23,by decide⟩).lower ∧ (cell12354 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12354 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12354 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12354 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12354 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12354 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12354,cell12354,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12354 ⟨24,by decide⟩).lower ∧ (cell12354 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12354 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12354 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12354 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12354 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12354 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12354,cell12354,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12354 ⟨25,by decide⟩).lower ∧ (cell12354 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12354 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12354 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12354 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12354 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12354 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12354,cell12354,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12354 ⟨26,by decide⟩).lower ∧ (cell12354 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12354 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12354 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12354 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12354 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12354 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12354,cell12354,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12354 ⟨27,by decide⟩).lower ∧ (cell12354 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12354 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12354 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12354 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12354 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12354 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12354,cell12354,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12354 ⟨28,by decide⟩).lower ∧ (cell12354 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12354 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12354 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12354 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12354 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12354 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12354,cell12354,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12354 ⟨29,by decide⟩).lower ∧ (cell12354 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12354 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12354 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12354 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12354 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12354 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12354,cell12354,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12354 ⟨30,by decide⟩).lower ∧ (cell12354 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12354 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12354 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12354 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12354 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12354 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12354,cell12354,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12354 ⟨31,by decide⟩).lower ∧ (cell12354 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12354 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12354 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12354 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12354 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12354 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12354,cell12354,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12354 ⟨32,by decide⟩).lower ∧ (cell12354 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12354 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12354 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12354 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12354 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12354 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12354,cell12354,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12354 ⟨33,by decide⟩).lower ∧ (cell12354 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12354 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12354 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12354 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12354 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12354 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12354,cell12354,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12354 ⟨34,by decide⟩).lower ∧ (cell12354 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12354 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12354 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12354 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12354 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12354 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12354,cell12354,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12354 ⟨35,by decide⟩).lower ∧ (cell12354 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12354 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12354 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12354 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12354 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12354 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12354,cell12354,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12354 ⟨36,by decide⟩).lower ∧ (cell12354 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12354 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12354 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12354 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12354 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12354 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12354,cell12354,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12354 ⟨37,by decide⟩).lower ∧ (cell12354 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12354 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12354 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12354 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12354 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12354 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12354,cell12354,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12354 ⟨38,by decide⟩).lower ∧ (cell12354 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12354 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12354 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12354 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12354 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12354 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12354,cell12354,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12354 ⟨39,by decide⟩).lower ∧ (cell12354 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12354 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12354 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12354 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12354 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12354 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12354,cell12354,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12354 ⟨40,by decide⟩).lower ∧ (cell12354 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12354 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12354 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12354 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12354 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12354 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12354,cell12354,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12354 ⟨41,by decide⟩).lower ∧ (cell12354 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12354 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12354 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12354 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12354 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12354 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12354,cell12354,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12354 ⟨42,by decide⟩).lower ∧ (cell12354 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12354 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12354 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12354 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12354 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12354 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12354,cell12354,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12354 ⟨43,by decide⟩).lower ∧ (cell12354 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12354 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12354 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12354 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12354 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12354 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12354,cell12354,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12354 ⟨44,by decide⟩).lower ∧ (cell12354 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12354 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12354 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12354 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12354 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12354 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12354,cell12354,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12354 ⟨45,by decide⟩).lower ∧ (cell12354 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12354 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12354 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12354 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12354 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12354 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12354,cell12354,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12354 ⟨46,by decide⟩).lower ∧ (cell12354 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12354 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12354 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12354 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12354 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12354 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12354,cell12354,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12354 ⟨47,by decide⟩).lower ∧ (cell12354 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12354 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12354 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12354 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12354 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12354 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12354,cell12354,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12354 ⟨48,by decide⟩).lower ∧ (cell12354 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12354 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12354 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12354 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12354 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12354 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12354,cell12354,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12354 ⟨49,by decide⟩).lower ∧ (cell12354 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12354 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12354 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12354 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12354 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12354 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12354,cell12354,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12354 ⟨50,by decide⟩).lower ∧ (cell12354 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12354 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12354 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12354 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12354 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12354 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12354,cell12354,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12354 ⟨51,by decide⟩).lower ∧ (cell12354 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12354 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12354 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12354 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12354 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12354 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12354,cell12354,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12354 ⟨52,by decide⟩).lower ∧ (cell12354 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12354 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12354 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12354 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12354 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12354 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12354,cell12354,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12354 i).lower ∧
    (cell12354 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12354 i).upper ≤ (0.532 : ℝ) ∧
    (cell12354 i).centre ≤ (0.1 : ℝ) ∧ (cell12354 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12354 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12354 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12354

/-! The local source numeric instances at 12354 have no network premises. -/
namespace BstLean.Part269.N12354
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12354)
open BstLean.Part268 (cell12354)

noncomputable def sourceNumerics12354 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12354 (cell12354 i)
      scalarRow12354.M scalarRow12354.H scalarRow12354.xi := by
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
    energy_allowance := scalarRow12354.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12354]
    centre_nonneg := (scalarRow12354.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D0.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12354])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12354
/-! Actual 12355 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12355
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12355 ≤ (1.036310173256 : ℝ) := by
  have hr : (111.153047641528 : ℝ) ≤ √(12355 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.153047641528 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12355 12355 (11 / 1000) ≤
    (0.008599738397 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12355) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.153047641528 : ℝ) ≤ √(12355 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12355)
  have hdiv : K / √(12355 : ℝ) ≤ K / 111.153047641528 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.153047641528 ≤ (0.008599738397 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12355.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12355 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12355 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12355 := gPlus_lower 12355
end BstLean.Part269.N12355

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12355
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036310173255 : ℝ) ≤ wn 12355 := by
  have hn : √(12355 : ℝ) ≤ 111.153047641529 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12355 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.153047641529 ≤ 2 / √(12355 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000259039589 : ℝ) ≤ rhoBar 12355 BstLean.Part154.csC ∧
    rhoBar 12355 BstLean.Part154.csC ≤ 0.000259039990 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036310173255 : ℝ) / (1.295212 * 12355) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036310173256 : ℝ) / (1.29521 * 12355) := by gcongr
      _ ≤ (0.000259039990 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12355 BstLean.Part154.csC) ≤ 0.001036227062 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12355 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12355 BstLean.Part154.csC) (piBar (rhoBar 12355 BstLean.Part154.csC)) ≤ 0.000197856753 ∧
    cc1 (rhoBar 12355 BstLean.Part154.csC) (piBar (rhoBar 12355 BstLean.Part154.csC)) ≤ 0.000125897512 ∧
    cc2 (rhoBar 12355 BstLean.Part154.csC) ≤ 0.000073084405 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12355 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12355 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12355 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12355 BstLean.Part154.csC * nuR (rhoBar 12355 BstLean.Part154.csC)) ≤ 0.000518096756 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000259039990 : ℝ) * 0.001036227062 := by gcongr
      _ ≤ (0.000518096756 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12355 BstLean.Part154.csC) * nuR (rhoBar 12355 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001036227062 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12355 BstLean.Part154.csC) * rhoBar 12355 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000259039990 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000259039990 / 2 + 0.399 * 0.001036227062 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000197856753 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000518096756 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125897512 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000259039990 / 1.414213562 := by gcongr
      _ ≤ (0.000073084405 : ℝ) := by norm_num

end BstLean.Part269.N12355

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12355
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12355 BstLean.Part154.csC) (piBar (rhoBar 12355 BstLean.Part154.csC)) ≤ 1.69058E-7 := by
  have hr0 : 0 ≤ rhoBar 12355 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12355 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12355 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12355 BstLean.Part154.csC) (piBar (rhoBar 12355 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12355 BstLean.Part154.csC) (piBar (rhoBar 12355 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12355 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000197856753 : ℝ) ^ 2 + 0.000125897512 ^ 2 + 3 * 0.000073084405 ^ 2 +
        2 * 0.797885 * 0.000197856753 * 0.000125897512 + 2 * 0.000197856753 * 0.000073084405 +
        4 * 0.797885 * 0.000125897512 * 0.000073084405 := by gcongr
    _ ≤ (1.69058E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12355 BstLean.Part154.csC Θ ≤ 0.002705324325 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12355 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12355 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12355 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12355 BstLean.Part154.csC) (piBar (rhoBar 12355 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12355 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036310173256 * 1.69058E-7 / (0.000259039589 : ℝ) := by gcongr
    _ ≤ 0.002705324325 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12355 BstLean.Part154.csC Θ ≤ 0.003003159953 + 0.000683591700 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12355 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12355 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12355 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036310173256 : ℝ) * ((2 * Θ * 0.000259039990 +
        (6863 / 10000) * 0.000259039990 * 12355 * 0.001036227062) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003003159953 + 0.000683591700 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12355 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12355 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12355 0.011 Θ ∧ gammaRatio 12355 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12355 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036310173256 : ℝ) * 0.525 / ((1 - 0.011) * 12355) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12355 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12355 0.011 Θ) :=
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
    badAllowance 12355 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12355 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12355 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12355 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12355 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12355 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12355 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12355 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12355 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12355 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12355 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036310173256 : ℝ) * 12355 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12355 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004103159953 + 0.003388916025 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12355

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12355
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12355 BstLean.Part154.csC) (piBar (rhoBar 12355 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12355 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12355 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12355 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12355 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12355 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12355 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12355 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12355 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12355 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12355 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12355 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12355 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12355 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12355 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053220051883 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12355) ≤ 0.010744083104 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12355 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036310173256)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010744083104 + 2 * 0.737676 / 12355) := by gcongr
    _ ≤ (0.053220051883 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12355 12 ≤ 0.0015 := by
  exact BstLean.Part269.S0.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12355

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12355
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560487530700 : ℝ) ≤ plow 12355 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12355) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053388940867)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001420295271) : eMP 12355 0.011 xi bn ≤ 0.001222304775 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12355 : ℝ) * (1 - 0.011))) ≤ 0.000604289100 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001420295271 / (12355 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000604289100 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000604289100 : ℝ) + 3.141593 * 0.053388940867 / (12355 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001222304775 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053388940867)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001420295271) : PiBarMP 12355 12 0.011 xi bn ≤ 0.163511616660 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12355 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037686804999 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.540015379047 : ℝ) ≤ √((12355 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.153047641528 : ℝ) ≤ √(12355 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12355) ≤ 0.125344365795 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037686804999 + 0.053388940867 * 1.772454 / (2 * (110.540015379047 : ℝ))) * (1 + 0.001222304775) +
        8 / (12355 * 111.153047641528) + 0.125344365795 := by gcongr
    _ ≤ (0.163511616660 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053388940867)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001420295271) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284280522036) :
    parallelOracle 12355 0.011 xi bn cd ≤ 0.164533276315 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12355 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12355 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560487530700 : ℝ) ≤ plow 12355 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.153047641528 : ℝ) ≤ √(12355 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284280522036 : ℝ) / (2 * 0.560487530700 * 111.153047641528)) * 0.163511616660 +
        0.284280522036 ^ 2 / (2 * 0.560487530700 * 111.153047641528) := by gcongr
    _ ≤ (0.164533276315 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053388940867) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001420295271)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284280522036) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12355 12355 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560487530700 : ℝ) ≤ plow 12355 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.153047641528 : ℝ) ≤ √(12355 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12355 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12355 Θ 1.22 ≤ 0.011930401624 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.153047641528 := by gcongr <;> linarith
      _ ≤ (0.011930401624 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12355 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12355 12355 0.011 ≤ 0.008599738397 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12355 12355 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12355 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12355 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12355 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12355 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164533276315 + 0.011930401624 + (0.008599738397 : ℝ) *
        (1 + 2 * (0.284280522036 + 0.011930401624) / (0.560487530700 * 111.153047641528))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12355]

end BstLean.Part269.N12355

/-! The original eight local profiles supply actual 12355 moment certificates. -/
namespace BstLean.Part269.N12355
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12355 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12355 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12355 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053388940867 ∧
    0 ≤ bN 12355 BstLean.Part154.csC (groupTheta g) ∧ bN 12355 BstLean.Part154.csC (groupTheta g) ≤ 0.001420295271 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12355 12355 0.011
      (momentAllowance 12355 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12355 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12355 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12355 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12355 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12355 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231060470153 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12355 0.011
      (momentAllowance 12355 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12355 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12355
/-! The actual computed-centre upper energy formula at 12355. -/
namespace BstLean.Part269.N12355
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12355

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12355
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12355)
open BstLean.Part268 (cell12355)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086569319796
  | 2 => 0.087533647240
  | 3 => 0.088499535713
  | 4 => 0.089469169381
  | 5 => 0.090445160976
  | 6 => 0.091430611537
  | 7 => 0.092429175077
  | 8 => 0.093445128105
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12355 12355 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12355 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004104440387 + 0.003390347157 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S0.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12355

/-! Actual upper energy certificates on all 43 source endpoints at 12355. -/
namespace BstLean.Part269.N12355
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12355)
open BstLean.Part268 (cell12355)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12355 (gMinus 12355) (1 - (cell12355 i).lower) ≤ 1 ∧
    energyUpper 12355 (gMinus 12355) (BstLean.Part211.gPlus 12355)
      (finiteEnergy 12355 12355 0.011) (1 - (cell12355 i).lower) ≤
      (cell12355 i).energy := by
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
      have E := BstLean.Part269.S0.uniformEnergy10 (n := 12355) (by norm_num)
        (q := 1 - (cell12355 ⟨10,by decide⟩).lower)
        (by norm_num [cell12355]) (by norm_num [cell12355])
      exact ⟨E.1,E.2.trans (by norm_num [cell12355])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy11 (n := 12355) (by norm_num)
        (q := 1 - (cell12355 ⟨11,by decide⟩).lower)
        (by norm_num [cell12355]) (by norm_num [cell12355])
      exact ⟨E.1,E.2.trans (by norm_num [cell12355])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy12 (n := 12355) (by norm_num)
        (q := 1 - (cell12355 ⟨12,by decide⟩).lower)
        (by norm_num [cell12355]) (by norm_num [cell12355])
      exact ⟨E.1,E.2.trans (by norm_num [cell12355])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy13 (n := 12355) (by norm_num)
        (q := 1 - (cell12355 ⟨13,by decide⟩).lower)
        (by norm_num [cell12355]) (by norm_num [cell12355])
      exact ⟨E.1,E.2.trans (by norm_num [cell12355])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy14 (n := 12355) (by norm_num)
        (q := 1 - (cell12355 ⟨14,by decide⟩).lower)
        (by norm_num [cell12355]) (by norm_num [cell12355])
      exact ⟨E.1,E.2.trans (by norm_num [cell12355])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy15 (n := 12355) (by norm_num)
        (q := 1 - (cell12355 ⟨15,by decide⟩).lower)
        (by norm_num [cell12355]) (by norm_num [cell12355])
      exact ⟨E.1,E.2.trans (by norm_num [cell12355])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy16 (n := 12355) (by norm_num)
        (q := 1 - (cell12355 ⟨16,by decide⟩).lower)
        (by norm_num [cell12355]) (by norm_num [cell12355])
      exact ⟨E.1,E.2.trans (by norm_num [cell12355])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy17 (n := 12355) (by norm_num)
        (q := 1 - (cell12355 ⟨17,by decide⟩).lower)
        (by norm_num [cell12355]) (by norm_num [cell12355])
      exact ⟨E.1,E.2.trans (by norm_num [cell12355])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy18 (n := 12355) (by norm_num)
        (q := 1 - (cell12355 ⟨18,by decide⟩).lower)
        (by norm_num [cell12355]) (by norm_num [cell12355])
      exact ⟨E.1,E.2.trans (by norm_num [cell12355])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy19 (n := 12355) (by norm_num)
        (q := 1 - (cell12355 ⟨19,by decide⟩).lower)
        (by norm_num [cell12355]) (by norm_num [cell12355])
      exact ⟨E.1,E.2.trans (by norm_num [cell12355])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy20 (n := 12355) (by norm_num)
        (q := 1 - (cell12355 ⟨20,by decide⟩).lower)
        (by norm_num [cell12355]) (by norm_num [cell12355])
      exact ⟨E.1,E.2.trans (by norm_num [cell12355])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy21 (n := 12355) (by norm_num)
        (q := 1 - (cell12355 ⟨21,by decide⟩).lower)
        (by norm_num [cell12355]) (by norm_num [cell12355])
      exact ⟨E.1,E.2.trans (by norm_num [cell12355])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy22 (n := 12355) (by norm_num)
        (q := 1 - (cell12355 ⟨22,by decide⟩).lower)
        (by norm_num [cell12355]) (by norm_num [cell12355])
      exact ⟨E.1,E.2.trans (by norm_num [cell12355])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy23 (n := 12355) (by norm_num)
        (q := 1 - (cell12355 ⟨23,by decide⟩).lower)
        (by norm_num [cell12355]) (by norm_num [cell12355])
      exact ⟨E.1,E.2.trans (by norm_num [cell12355])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy24 (n := 12355) (by norm_num)
        (q := 1 - (cell12355 ⟨24,by decide⟩).lower)
        (by norm_num [cell12355]) (by norm_num [cell12355])
      exact ⟨E.1,E.2.trans (by norm_num [cell12355])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy25 (n := 12355) (by norm_num)
        (q := 1 - (cell12355 ⟨25,by decide⟩).lower)
        (by norm_num [cell12355]) (by norm_num [cell12355])
      exact ⟨E.1,E.2.trans (by norm_num [cell12355])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy26 (n := 12355) (by norm_num)
        (q := 1 - (cell12355 ⟨26,by decide⟩).lower)
        (by norm_num [cell12355]) (by norm_num [cell12355])
      exact ⟨E.1,E.2.trans (by norm_num [cell12355])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy27 (n := 12355) (by norm_num)
        (q := 1 - (cell12355 ⟨27,by decide⟩).lower)
        (by norm_num [cell12355]) (by norm_num [cell12355])
      exact ⟨E.1,E.2.trans (by norm_num [cell12355])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy28 (n := 12355) (by norm_num)
        (q := 1 - (cell12355 ⟨28,by decide⟩).lower)
        (by norm_num [cell12355]) (by norm_num [cell12355])
      exact ⟨E.1,E.2.trans (by norm_num [cell12355])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy29 (n := 12355) (by norm_num)
        (q := 1 - (cell12355 ⟨29,by decide⟩).lower)
        (by norm_num [cell12355]) (by norm_num [cell12355])
      exact ⟨E.1,E.2.trans (by norm_num [cell12355])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy30 (n := 12355) (by norm_num)
        (q := 1 - (cell12355 ⟨30,by decide⟩).lower)
        (by norm_num [cell12355]) (by norm_num [cell12355])
      exact ⟨E.1,E.2.trans (by norm_num [cell12355])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy31 (n := 12355) (by norm_num)
        (q := 1 - (cell12355 ⟨31,by decide⟩).lower)
        (by norm_num [cell12355]) (by norm_num [cell12355])
      exact ⟨E.1,E.2.trans (by norm_num [cell12355])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy32 (n := 12355) (by norm_num)
        (q := 1 - (cell12355 ⟨32,by decide⟩).lower)
        (by norm_num [cell12355]) (by norm_num [cell12355])
      exact ⟨E.1,E.2.trans (by norm_num [cell12355])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy33 (n := 12355) (by norm_num)
        (q := 1 - (cell12355 ⟨33,by decide⟩).lower)
        (by norm_num [cell12355]) (by norm_num [cell12355])
      exact ⟨E.1,E.2.trans (by norm_num [cell12355])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy34 (n := 12355) (by norm_num)
        (q := 1 - (cell12355 ⟨34,by decide⟩).lower)
        (by norm_num [cell12355]) (by norm_num [cell12355])
      exact ⟨E.1,E.2.trans (by norm_num [cell12355])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy35 (n := 12355) (by norm_num)
        (q := 1 - (cell12355 ⟨35,by decide⟩).lower)
        (by norm_num [cell12355]) (by norm_num [cell12355])
      exact ⟨E.1,E.2.trans (by norm_num [cell12355])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy36 (n := 12355) (by norm_num)
        (q := 1 - (cell12355 ⟨36,by decide⟩).lower)
        (by norm_num [cell12355]) (by norm_num [cell12355])
      exact ⟨E.1,E.2.trans (by norm_num [cell12355])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy37 (n := 12355) (by norm_num)
        (q := 1 - (cell12355 ⟨37,by decide⟩).lower)
        (by norm_num [cell12355]) (by norm_num [cell12355])
      exact ⟨E.1,E.2.trans (by norm_num [cell12355])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy38 (n := 12355) (by norm_num)
        (q := 1 - (cell12355 ⟨38,by decide⟩).lower)
        (by norm_num [cell12355]) (by norm_num [cell12355])
      exact ⟨E.1,E.2.trans (by norm_num [cell12355])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy39 (n := 12355) (by norm_num)
        (q := 1 - (cell12355 ⟨39,by decide⟩).lower)
        (by norm_num [cell12355]) (by norm_num [cell12355])
      exact ⟨E.1,E.2.trans (by norm_num [cell12355])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy40 (n := 12355) (by norm_num)
        (q := 1 - (cell12355 ⟨40,by decide⟩).lower)
        (by norm_num [cell12355]) (by norm_num [cell12355])
      exact ⟨E.1,E.2.trans (by norm_num [cell12355])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy41 (n := 12355) (by norm_num)
        (q := 1 - (cell12355 ⟨41,by decide⟩).lower)
        (by norm_num [cell12355]) (by norm_num [cell12355])
      exact ⟨E.1,E.2.trans (by norm_num [cell12355])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy42 (n := 12355) (by norm_num)
        (q := 1 - (cell12355 ⟨42,by decide⟩).lower)
        (by norm_num [cell12355]) (by norm_num [cell12355])
      exact ⟨E.1,E.2.trans (by norm_num [cell12355])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy43 (n := 12355) (by norm_num)
        (q := 1 - (cell12355 ⟨43,by decide⟩).lower)
        (by norm_num [cell12355]) (by norm_num [cell12355])
      exact ⟨E.1,E.2.trans (by norm_num [cell12355])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy44 (n := 12355) (by norm_num)
        (q := 1 - (cell12355 ⟨44,by decide⟩).lower)
        (by norm_num [cell12355]) (by norm_num [cell12355])
      exact ⟨E.1,E.2.trans (by norm_num [cell12355])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy45 (n := 12355) (by norm_num)
        (q := 1 - (cell12355 ⟨45,by decide⟩).lower)
        (by norm_num [cell12355]) (by norm_num [cell12355])
      exact ⟨E.1,E.2.trans (by norm_num [cell12355])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy46 (n := 12355) (by norm_num)
        (q := 1 - (cell12355 ⟨46,by decide⟩).lower)
        (by norm_num [cell12355]) (by norm_num [cell12355])
      exact ⟨E.1,E.2.trans (by norm_num [cell12355])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy47 (n := 12355) (by norm_num)
        (q := 1 - (cell12355 ⟨47,by decide⟩).lower)
        (by norm_num [cell12355]) (by norm_num [cell12355])
      exact ⟨E.1,E.2.trans (by norm_num [cell12355])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy48 (n := 12355) (by norm_num)
        (q := 1 - (cell12355 ⟨48,by decide⟩).lower)
        (by norm_num [cell12355]) (by norm_num [cell12355])
      exact ⟨E.1,E.2.trans (by norm_num [cell12355])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy49 (n := 12355) (by norm_num)
        (q := 1 - (cell12355 ⟨49,by decide⟩).lower)
        (by norm_num [cell12355]) (by norm_num [cell12355])
      exact ⟨E.1,E.2.trans (by norm_num [cell12355])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy50 (n := 12355) (by norm_num)
        (q := 1 - (cell12355 ⟨50,by decide⟩).lower)
        (by norm_num [cell12355]) (by norm_num [cell12355])
      exact ⟨E.1,E.2.trans (by norm_num [cell12355])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy51 (n := 12355) (by norm_num)
        (q := 1 - (cell12355 ⟨51,by decide⟩).lower)
        (by norm_num [cell12355]) (by norm_num [cell12355])
      exact ⟨E.1,E.2.trans (by norm_num [cell12355])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy52 (n := 12355) (by norm_num)
        (q := 1 - (cell12355 ⟨52,by decide⟩).lower)
        (by norm_num [cell12355]) (by norm_num [cell12355])
      exact ⟨E.1,E.2.trans (by norm_num [cell12355])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12355

/-! Source-cell containment and simple scalar guards at 12355. -/
namespace BstLean.Part269.N12355
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12355)
open BstLean.Part268 (cell12355)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12355 ⟨10,by decide⟩).lower ∧ (cell12355 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12355 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12355 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12355 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12355 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12355 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12355,cell12355,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12355 ⟨11,by decide⟩).lower ∧ (cell12355 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12355 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12355 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12355 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12355 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12355 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12355,cell12355,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12355 ⟨12,by decide⟩).lower ∧ (cell12355 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12355 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12355 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12355 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12355 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12355 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12355,cell12355,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12355 ⟨13,by decide⟩).lower ∧ (cell12355 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12355 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12355 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12355 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12355 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12355 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12355,cell12355,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12355 ⟨14,by decide⟩).lower ∧ (cell12355 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12355 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12355 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12355 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12355 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12355 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12355,cell12355,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12355 ⟨15,by decide⟩).lower ∧ (cell12355 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12355 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12355 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12355 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12355 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12355 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12355,cell12355,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12355 ⟨16,by decide⟩).lower ∧ (cell12355 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12355 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12355 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12355 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12355 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12355 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12355,cell12355,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12355 ⟨17,by decide⟩).lower ∧ (cell12355 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12355 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12355 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12355 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12355 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12355 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12355,cell12355,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12355 ⟨18,by decide⟩).lower ∧ (cell12355 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12355 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12355 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12355 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12355 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12355 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12355,cell12355,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12355 ⟨19,by decide⟩).lower ∧ (cell12355 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12355 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12355 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12355 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12355 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12355 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12355,cell12355,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12355 ⟨20,by decide⟩).lower ∧ (cell12355 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12355 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12355 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12355 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12355 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12355 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12355,cell12355,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12355 ⟨21,by decide⟩).lower ∧ (cell12355 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12355 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12355 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12355 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12355 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12355 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12355,cell12355,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12355 ⟨22,by decide⟩).lower ∧ (cell12355 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12355 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12355 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12355 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12355 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12355 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12355,cell12355,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12355 ⟨23,by decide⟩).lower ∧ (cell12355 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12355 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12355 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12355 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12355 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12355 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12355,cell12355,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12355 ⟨24,by decide⟩).lower ∧ (cell12355 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12355 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12355 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12355 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12355 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12355 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12355,cell12355,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12355 ⟨25,by decide⟩).lower ∧ (cell12355 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12355 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12355 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12355 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12355 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12355 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12355,cell12355,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12355 ⟨26,by decide⟩).lower ∧ (cell12355 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12355 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12355 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12355 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12355 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12355 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12355,cell12355,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12355 ⟨27,by decide⟩).lower ∧ (cell12355 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12355 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12355 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12355 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12355 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12355 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12355,cell12355,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12355 ⟨28,by decide⟩).lower ∧ (cell12355 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12355 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12355 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12355 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12355 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12355 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12355,cell12355,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12355 ⟨29,by decide⟩).lower ∧ (cell12355 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12355 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12355 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12355 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12355 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12355 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12355,cell12355,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12355 ⟨30,by decide⟩).lower ∧ (cell12355 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12355 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12355 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12355 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12355 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12355 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12355,cell12355,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12355 ⟨31,by decide⟩).lower ∧ (cell12355 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12355 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12355 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12355 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12355 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12355 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12355,cell12355,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12355 ⟨32,by decide⟩).lower ∧ (cell12355 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12355 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12355 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12355 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12355 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12355 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12355,cell12355,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12355 ⟨33,by decide⟩).lower ∧ (cell12355 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12355 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12355 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12355 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12355 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12355 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12355,cell12355,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12355 ⟨34,by decide⟩).lower ∧ (cell12355 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12355 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12355 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12355 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12355 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12355 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12355,cell12355,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12355 ⟨35,by decide⟩).lower ∧ (cell12355 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12355 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12355 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12355 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12355 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12355 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12355,cell12355,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12355 ⟨36,by decide⟩).lower ∧ (cell12355 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12355 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12355 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12355 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12355 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12355 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12355,cell12355,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12355 ⟨37,by decide⟩).lower ∧ (cell12355 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12355 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12355 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12355 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12355 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12355 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12355,cell12355,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12355 ⟨38,by decide⟩).lower ∧ (cell12355 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12355 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12355 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12355 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12355 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12355 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12355,cell12355,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12355 ⟨39,by decide⟩).lower ∧ (cell12355 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12355 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12355 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12355 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12355 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12355 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12355,cell12355,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12355 ⟨40,by decide⟩).lower ∧ (cell12355 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12355 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12355 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12355 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12355 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12355 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12355,cell12355,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12355 ⟨41,by decide⟩).lower ∧ (cell12355 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12355 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12355 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12355 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12355 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12355 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12355,cell12355,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12355 ⟨42,by decide⟩).lower ∧ (cell12355 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12355 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12355 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12355 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12355 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12355 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12355,cell12355,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12355 ⟨43,by decide⟩).lower ∧ (cell12355 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12355 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12355 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12355 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12355 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12355 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12355,cell12355,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12355 ⟨44,by decide⟩).lower ∧ (cell12355 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12355 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12355 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12355 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12355 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12355 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12355,cell12355,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12355 ⟨45,by decide⟩).lower ∧ (cell12355 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12355 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12355 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12355 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12355 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12355 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12355,cell12355,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12355 ⟨46,by decide⟩).lower ∧ (cell12355 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12355 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12355 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12355 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12355 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12355 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12355,cell12355,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12355 ⟨47,by decide⟩).lower ∧ (cell12355 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12355 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12355 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12355 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12355 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12355 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12355,cell12355,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12355 ⟨48,by decide⟩).lower ∧ (cell12355 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12355 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12355 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12355 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12355 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12355 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12355,cell12355,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12355 ⟨49,by decide⟩).lower ∧ (cell12355 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12355 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12355 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12355 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12355 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12355 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12355,cell12355,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12355 ⟨50,by decide⟩).lower ∧ (cell12355 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12355 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12355 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12355 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12355 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12355 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12355,cell12355,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12355 ⟨51,by decide⟩).lower ∧ (cell12355 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12355 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12355 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12355 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12355 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12355 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12355,cell12355,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12355 ⟨52,by decide⟩).lower ∧ (cell12355 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12355 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12355 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12355 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12355 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12355 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12355,cell12355,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12355 i).lower ∧
    (cell12355 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12355 i).upper ≤ (0.532 : ℝ) ∧
    (cell12355 i).centre ≤ (0.1 : ℝ) ∧ (cell12355 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12355 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12355 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12355

/-! The local source numeric instances at 12355 have no network premises. -/
namespace BstLean.Part269.N12355
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12355)
open BstLean.Part268 (cell12355)

noncomputable def sourceNumerics12355 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12355 (cell12355 i)
      scalarRow12355.M scalarRow12355.H scalarRow12355.xi := by
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
    energy_allowance := scalarRow12355.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12355]
    centre_nonneg := (scalarRow12355.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D0.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12355])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12355
/-! Actual 12356 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12356
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12356 ≤ (1.036308690791 : ℝ) := by
  have hr : (111.157545852722 : ℝ) ≤ √(12356 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.157545852722 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12356 12356 (11 / 1000) ≤
    (0.008599390389 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12356) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.157545852722 : ℝ) ≤ √(12356 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12356)
  have hdiv : K / √(12356 : ℝ) ≤ K / 111.157545852722 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.157545852722 ≤ (0.008599390389 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12356.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12356 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12356 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12356 := gPlus_lower 12356
end BstLean.Part269.N12356

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12356
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036308690790 : ℝ) ≤ wn 12356 := by
  have hn : √(12356 : ℝ) ≤ 111.157545852723 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12356 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.157545852723 ≤ 2 / √(12356 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000259018254 : ℝ) ≤ rhoBar 12356 BstLean.Part154.csC ∧
    rhoBar 12356 BstLean.Part154.csC ≤ 0.000259018655 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036308690790 : ℝ) / (1.295212 * 12356) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036308690791 : ℝ) / (1.29521 * 12356) := by gcongr
      _ ≤ (0.000259018655 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12356 BstLean.Part154.csC) ≤ 0.001036141711 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12356 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12356 BstLean.Part154.csC) (piBar (rhoBar 12356 BstLean.Part154.csC)) ≤ 0.000197840457 ∧
    cc1 (rhoBar 12356 BstLean.Part154.csC) (piBar (rhoBar 12356 BstLean.Part154.csC)) ≤ 0.000125887143 ∧
    cc2 (rhoBar 12356 BstLean.Part154.csC) ≤ 0.000073078386 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12356 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12356 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12356 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12356 BstLean.Part154.csC * nuR (rhoBar 12356 BstLean.Part154.csC)) ≤ 0.000518054083 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000259018655 : ℝ) * 0.001036141711 := by gcongr
      _ ≤ (0.000518054083 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12356 BstLean.Part154.csC) * nuR (rhoBar 12356 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001036141711 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12356 BstLean.Part154.csC) * rhoBar 12356 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000259018655 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000259018655 / 2 + 0.399 * 0.001036141711 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000197840457 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000518054083 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125887143 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000259018655 / 1.414213562 := by gcongr
      _ ≤ (0.000073078386 : ℝ) := by norm_num

end BstLean.Part269.N12356

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12356
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12356 BstLean.Part154.csC) (piBar (rhoBar 12356 BstLean.Part154.csC)) ≤ 1.69031E-7 := by
  have hr0 : 0 ≤ rhoBar 12356 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12356 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12356 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12356 BstLean.Part154.csC) (piBar (rhoBar 12356 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12356 BstLean.Part154.csC) (piBar (rhoBar 12356 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12356 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000197840457 : ℝ) ^ 2 + 0.000125887143 ^ 2 + 3 * 0.000073078386 ^ 2 +
        2 * 0.797885 * 0.000197840457 * 0.000125887143 + 2 * 0.000197840457 * 0.000073078386 +
        4 * 0.797885 * 0.000125887143 * 0.000073078386 := by gcongr
    _ ≤ (1.69031E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12356 BstLean.Part154.csC Θ ≤ 0.002705111190 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12356 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12356 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12356 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12356 BstLean.Part154.csC) (piBar (rhoBar 12356 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12356 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036308690791 * 1.69031E-7 / (0.000259018254 : ℝ) := by gcongr
    _ ≤ 0.002705111190 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12356 BstLean.Part154.csC Θ ≤ 0.003002904003 + 0.000683534421 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12356 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12356 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12356 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036308690791 : ℝ) * ((2 * Θ * 0.000259018655 +
        (6863 / 10000) * 0.000259018655 * 12356 * 0.001036141711) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003002904003 + 0.000683534421 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12356 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12356 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12356 0.011 Θ ∧ gammaRatio 12356 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12356 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036308690791 : ℝ) * 0.525 / ((1 - 0.011) * 12356) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12356 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12356 0.011 Θ) :=
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
    badAllowance 12356 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12356 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12356 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12356 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12356 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12356 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12356 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12356 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12356 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12356 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12356 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036308690791 : ℝ) * 12356 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12356 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004102904003 + 0.003388645611 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12356

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12356
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12356 BstLean.Part154.csC) (piBar (rhoBar 12356 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12356 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12356 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12356 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12356 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12356 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12356 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12356 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12356 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12356 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12356 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12356 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12356 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12356 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12356 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053217874554 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12356) ≤ 0.010743648323 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12356 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036308690791)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010743648323 + 2 * 0.737676 / 12356) := by gcongr
    _ ≤ (0.053217874554 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12356 12 ≤ 0.0015 := by
  exact BstLean.Part269.S0.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12356

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12356
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560487578480 : ℝ) ≤ plow 12356 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12356) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053388542949)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001420183375) : eMP 12356 0.011 xi bn ≤ 0.001222207048 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12356 : ℝ) * (1 - 0.011))) ≤ 0.000604240843 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001420183375 / (12356 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000604240843 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000604240843 : ℝ) + 3.141593 * 0.053388542949 / (12356 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001222207048 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053388542949)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001420183375) : PiBarMP 12356 12 0.011 xi bn ≤ 0.163505032987 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12356 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037685320418 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.544488781666 : ℝ) ≤ √((12356 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.157545852722 : ℝ) ≤ √(12356 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12356) ≤ 0.125339293486 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037685320418 + 0.053388542949 * 1.772454 / (2 * (110.544488781666 : ℝ))) * (1 + 0.001222207048) +
        8 / (12356 * 111.157545852722) + 0.125339293486 := by gcongr
    _ ≤ (0.163505032987 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053388542949)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001420183375) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284277483636) :
    parallelOracle 12356 0.011 xi bn cd ≤ 0.164526618341 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12356 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12356 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560487578480 : ℝ) ≤ plow 12356 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.157545852722 : ℝ) ≤ √(12356 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284277483636 : ℝ) / (2 * 0.560487578480 * 111.157545852722)) * 0.163505032987 +
        0.284277483636 ^ 2 / (2 * 0.560487578480 * 111.157545852722) := by gcongr
    _ ≤ (0.164526618341 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053388542949) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001420183375)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284277483636) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12356 12356 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560487578480 : ℝ) ≤ plow 12356 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.157545852722 : ℝ) ≤ √(12356 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12356 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12356 Θ 1.22 ≤ 0.011929918836 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.157545852722 := by gcongr <;> linarith
      _ ≤ (0.011929918836 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12356 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12356 12356 0.011 ≤ 0.008599390389 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12356 12356 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12356 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12356 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12356 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12356 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164526618341 + 0.011929918836 + (0.008599390389 : ℝ) *
        (1 + 2 * (0.284277483636 + 0.011929918836) / (0.560487578480 * 111.157545852722))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12356]

end BstLean.Part269.N12356

/-! The original eight local profiles supply actual 12356 moment certificates. -/
namespace BstLean.Part269.N12356
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12356 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12356 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12356 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053388542949 ∧
    0 ≤ bN 12356 BstLean.Part154.csC (groupTheta g) ∧ bN 12356 BstLean.Part154.csC (groupTheta g) ≤ 0.001420183375 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12356 12356 0.011
      (momentAllowance 12356 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12356 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12356 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12356 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12356 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12356 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231059609082 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12356 0.011
      (momentAllowance 12356 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12356 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12356
/-! The actual computed-centre upper energy formula at 12356. -/
namespace BstLean.Part269.N12356
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12356

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12356
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12356)
open BstLean.Part268 (cell12356)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086565954057
  | 2 => 0.087530208569
  | 3 => 0.088496011768
  | 4 => 0.089465545125
  | 5 => 0.090441418221
  | 6 => 0.091426728445
  | 7 => 0.092425125606
  | 8 => 0.093440881393
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12356 12356 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12356 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004104440387 + 0.003390347157 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S0.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12356

/-! Actual upper energy certificates on all 43 source endpoints at 12356. -/
namespace BstLean.Part269.N12356
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12356)
open BstLean.Part268 (cell12356)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12356 (gMinus 12356) (1 - (cell12356 i).lower) ≤ 1 ∧
    energyUpper 12356 (gMinus 12356) (BstLean.Part211.gPlus 12356)
      (finiteEnergy 12356 12356 0.011) (1 - (cell12356 i).lower) ≤
      (cell12356 i).energy := by
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
      have E := BstLean.Part269.S0.uniformEnergy10 (n := 12356) (by norm_num)
        (q := 1 - (cell12356 ⟨10,by decide⟩).lower)
        (by norm_num [cell12356]) (by norm_num [cell12356])
      exact ⟨E.1,E.2.trans (by norm_num [cell12356])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy11 (n := 12356) (by norm_num)
        (q := 1 - (cell12356 ⟨11,by decide⟩).lower)
        (by norm_num [cell12356]) (by norm_num [cell12356])
      exact ⟨E.1,E.2.trans (by norm_num [cell12356])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy12 (n := 12356) (by norm_num)
        (q := 1 - (cell12356 ⟨12,by decide⟩).lower)
        (by norm_num [cell12356]) (by norm_num [cell12356])
      exact ⟨E.1,E.2.trans (by norm_num [cell12356])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy13 (n := 12356) (by norm_num)
        (q := 1 - (cell12356 ⟨13,by decide⟩).lower)
        (by norm_num [cell12356]) (by norm_num [cell12356])
      exact ⟨E.1,E.2.trans (by norm_num [cell12356])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy14 (n := 12356) (by norm_num)
        (q := 1 - (cell12356 ⟨14,by decide⟩).lower)
        (by norm_num [cell12356]) (by norm_num [cell12356])
      exact ⟨E.1,E.2.trans (by norm_num [cell12356])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy15 (n := 12356) (by norm_num)
        (q := 1 - (cell12356 ⟨15,by decide⟩).lower)
        (by norm_num [cell12356]) (by norm_num [cell12356])
      exact ⟨E.1,E.2.trans (by norm_num [cell12356])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy16 (n := 12356) (by norm_num)
        (q := 1 - (cell12356 ⟨16,by decide⟩).lower)
        (by norm_num [cell12356]) (by norm_num [cell12356])
      exact ⟨E.1,E.2.trans (by norm_num [cell12356])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy17 (n := 12356) (by norm_num)
        (q := 1 - (cell12356 ⟨17,by decide⟩).lower)
        (by norm_num [cell12356]) (by norm_num [cell12356])
      exact ⟨E.1,E.2.trans (by norm_num [cell12356])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy18 (n := 12356) (by norm_num)
        (q := 1 - (cell12356 ⟨18,by decide⟩).lower)
        (by norm_num [cell12356]) (by norm_num [cell12356])
      exact ⟨E.1,E.2.trans (by norm_num [cell12356])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy19 (n := 12356) (by norm_num)
        (q := 1 - (cell12356 ⟨19,by decide⟩).lower)
        (by norm_num [cell12356]) (by norm_num [cell12356])
      exact ⟨E.1,E.2.trans (by norm_num [cell12356])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy20 (n := 12356) (by norm_num)
        (q := 1 - (cell12356 ⟨20,by decide⟩).lower)
        (by norm_num [cell12356]) (by norm_num [cell12356])
      exact ⟨E.1,E.2.trans (by norm_num [cell12356])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy21 (n := 12356) (by norm_num)
        (q := 1 - (cell12356 ⟨21,by decide⟩).lower)
        (by norm_num [cell12356]) (by norm_num [cell12356])
      exact ⟨E.1,E.2.trans (by norm_num [cell12356])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy22 (n := 12356) (by norm_num)
        (q := 1 - (cell12356 ⟨22,by decide⟩).lower)
        (by norm_num [cell12356]) (by norm_num [cell12356])
      exact ⟨E.1,E.2.trans (by norm_num [cell12356])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy23 (n := 12356) (by norm_num)
        (q := 1 - (cell12356 ⟨23,by decide⟩).lower)
        (by norm_num [cell12356]) (by norm_num [cell12356])
      exact ⟨E.1,E.2.trans (by norm_num [cell12356])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy24 (n := 12356) (by norm_num)
        (q := 1 - (cell12356 ⟨24,by decide⟩).lower)
        (by norm_num [cell12356]) (by norm_num [cell12356])
      exact ⟨E.1,E.2.trans (by norm_num [cell12356])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy25 (n := 12356) (by norm_num)
        (q := 1 - (cell12356 ⟨25,by decide⟩).lower)
        (by norm_num [cell12356]) (by norm_num [cell12356])
      exact ⟨E.1,E.2.trans (by norm_num [cell12356])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy26 (n := 12356) (by norm_num)
        (q := 1 - (cell12356 ⟨26,by decide⟩).lower)
        (by norm_num [cell12356]) (by norm_num [cell12356])
      exact ⟨E.1,E.2.trans (by norm_num [cell12356])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy27 (n := 12356) (by norm_num)
        (q := 1 - (cell12356 ⟨27,by decide⟩).lower)
        (by norm_num [cell12356]) (by norm_num [cell12356])
      exact ⟨E.1,E.2.trans (by norm_num [cell12356])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy28 (n := 12356) (by norm_num)
        (q := 1 - (cell12356 ⟨28,by decide⟩).lower)
        (by norm_num [cell12356]) (by norm_num [cell12356])
      exact ⟨E.1,E.2.trans (by norm_num [cell12356])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy29 (n := 12356) (by norm_num)
        (q := 1 - (cell12356 ⟨29,by decide⟩).lower)
        (by norm_num [cell12356]) (by norm_num [cell12356])
      exact ⟨E.1,E.2.trans (by norm_num [cell12356])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy30 (n := 12356) (by norm_num)
        (q := 1 - (cell12356 ⟨30,by decide⟩).lower)
        (by norm_num [cell12356]) (by norm_num [cell12356])
      exact ⟨E.1,E.2.trans (by norm_num [cell12356])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy31 (n := 12356) (by norm_num)
        (q := 1 - (cell12356 ⟨31,by decide⟩).lower)
        (by norm_num [cell12356]) (by norm_num [cell12356])
      exact ⟨E.1,E.2.trans (by norm_num [cell12356])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy32 (n := 12356) (by norm_num)
        (q := 1 - (cell12356 ⟨32,by decide⟩).lower)
        (by norm_num [cell12356]) (by norm_num [cell12356])
      exact ⟨E.1,E.2.trans (by norm_num [cell12356])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy33 (n := 12356) (by norm_num)
        (q := 1 - (cell12356 ⟨33,by decide⟩).lower)
        (by norm_num [cell12356]) (by norm_num [cell12356])
      exact ⟨E.1,E.2.trans (by norm_num [cell12356])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy34 (n := 12356) (by norm_num)
        (q := 1 - (cell12356 ⟨34,by decide⟩).lower)
        (by norm_num [cell12356]) (by norm_num [cell12356])
      exact ⟨E.1,E.2.trans (by norm_num [cell12356])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy35 (n := 12356) (by norm_num)
        (q := 1 - (cell12356 ⟨35,by decide⟩).lower)
        (by norm_num [cell12356]) (by norm_num [cell12356])
      exact ⟨E.1,E.2.trans (by norm_num [cell12356])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy36 (n := 12356) (by norm_num)
        (q := 1 - (cell12356 ⟨36,by decide⟩).lower)
        (by norm_num [cell12356]) (by norm_num [cell12356])
      exact ⟨E.1,E.2.trans (by norm_num [cell12356])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy37 (n := 12356) (by norm_num)
        (q := 1 - (cell12356 ⟨37,by decide⟩).lower)
        (by norm_num [cell12356]) (by norm_num [cell12356])
      exact ⟨E.1,E.2.trans (by norm_num [cell12356])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy38 (n := 12356) (by norm_num)
        (q := 1 - (cell12356 ⟨38,by decide⟩).lower)
        (by norm_num [cell12356]) (by norm_num [cell12356])
      exact ⟨E.1,E.2.trans (by norm_num [cell12356])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy39 (n := 12356) (by norm_num)
        (q := 1 - (cell12356 ⟨39,by decide⟩).lower)
        (by norm_num [cell12356]) (by norm_num [cell12356])
      exact ⟨E.1,E.2.trans (by norm_num [cell12356])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy40 (n := 12356) (by norm_num)
        (q := 1 - (cell12356 ⟨40,by decide⟩).lower)
        (by norm_num [cell12356]) (by norm_num [cell12356])
      exact ⟨E.1,E.2.trans (by norm_num [cell12356])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy41 (n := 12356) (by norm_num)
        (q := 1 - (cell12356 ⟨41,by decide⟩).lower)
        (by norm_num [cell12356]) (by norm_num [cell12356])
      exact ⟨E.1,E.2.trans (by norm_num [cell12356])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy42 (n := 12356) (by norm_num)
        (q := 1 - (cell12356 ⟨42,by decide⟩).lower)
        (by norm_num [cell12356]) (by norm_num [cell12356])
      exact ⟨E.1,E.2.trans (by norm_num [cell12356])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy43 (n := 12356) (by norm_num)
        (q := 1 - (cell12356 ⟨43,by decide⟩).lower)
        (by norm_num [cell12356]) (by norm_num [cell12356])
      exact ⟨E.1,E.2.trans (by norm_num [cell12356])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy44 (n := 12356) (by norm_num)
        (q := 1 - (cell12356 ⟨44,by decide⟩).lower)
        (by norm_num [cell12356]) (by norm_num [cell12356])
      exact ⟨E.1,E.2.trans (by norm_num [cell12356])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy45 (n := 12356) (by norm_num)
        (q := 1 - (cell12356 ⟨45,by decide⟩).lower)
        (by norm_num [cell12356]) (by norm_num [cell12356])
      exact ⟨E.1,E.2.trans (by norm_num [cell12356])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy46 (n := 12356) (by norm_num)
        (q := 1 - (cell12356 ⟨46,by decide⟩).lower)
        (by norm_num [cell12356]) (by norm_num [cell12356])
      exact ⟨E.1,E.2.trans (by norm_num [cell12356])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy47 (n := 12356) (by norm_num)
        (q := 1 - (cell12356 ⟨47,by decide⟩).lower)
        (by norm_num [cell12356]) (by norm_num [cell12356])
      exact ⟨E.1,E.2.trans (by norm_num [cell12356])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy48 (n := 12356) (by norm_num)
        (q := 1 - (cell12356 ⟨48,by decide⟩).lower)
        (by norm_num [cell12356]) (by norm_num [cell12356])
      exact ⟨E.1,E.2.trans (by norm_num [cell12356])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy49 (n := 12356) (by norm_num)
        (q := 1 - (cell12356 ⟨49,by decide⟩).lower)
        (by norm_num [cell12356]) (by norm_num [cell12356])
      exact ⟨E.1,E.2.trans (by norm_num [cell12356])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy50 (n := 12356) (by norm_num)
        (q := 1 - (cell12356 ⟨50,by decide⟩).lower)
        (by norm_num [cell12356]) (by norm_num [cell12356])
      exact ⟨E.1,E.2.trans (by norm_num [cell12356])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy51 (n := 12356) (by norm_num)
        (q := 1 - (cell12356 ⟨51,by decide⟩).lower)
        (by norm_num [cell12356]) (by norm_num [cell12356])
      exact ⟨E.1,E.2.trans (by norm_num [cell12356])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy52 (n := 12356) (by norm_num)
        (q := 1 - (cell12356 ⟨52,by decide⟩).lower)
        (by norm_num [cell12356]) (by norm_num [cell12356])
      exact ⟨E.1,E.2.trans (by norm_num [cell12356])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12356

/-! Source-cell containment and simple scalar guards at 12356. -/
namespace BstLean.Part269.N12356
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12356)
open BstLean.Part268 (cell12356)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12356 ⟨10,by decide⟩).lower ∧ (cell12356 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12356 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12356 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12356 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12356 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12356 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12356,cell12356,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12356 ⟨11,by decide⟩).lower ∧ (cell12356 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12356 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12356 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12356 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12356 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12356 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12356,cell12356,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12356 ⟨12,by decide⟩).lower ∧ (cell12356 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12356 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12356 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12356 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12356 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12356 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12356,cell12356,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12356 ⟨13,by decide⟩).lower ∧ (cell12356 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12356 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12356 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12356 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12356 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12356 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12356,cell12356,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12356 ⟨14,by decide⟩).lower ∧ (cell12356 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12356 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12356 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12356 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12356 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12356 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12356,cell12356,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12356 ⟨15,by decide⟩).lower ∧ (cell12356 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12356 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12356 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12356 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12356 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12356 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12356,cell12356,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12356 ⟨16,by decide⟩).lower ∧ (cell12356 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12356 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12356 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12356 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12356 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12356 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12356,cell12356,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12356 ⟨17,by decide⟩).lower ∧ (cell12356 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12356 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12356 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12356 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12356 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12356 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12356,cell12356,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12356 ⟨18,by decide⟩).lower ∧ (cell12356 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12356 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12356 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12356 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12356 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12356 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12356,cell12356,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12356 ⟨19,by decide⟩).lower ∧ (cell12356 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12356 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12356 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12356 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12356 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12356 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12356,cell12356,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12356 ⟨20,by decide⟩).lower ∧ (cell12356 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12356 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12356 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12356 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12356 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12356 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12356,cell12356,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12356 ⟨21,by decide⟩).lower ∧ (cell12356 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12356 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12356 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12356 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12356 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12356 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12356,cell12356,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12356 ⟨22,by decide⟩).lower ∧ (cell12356 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12356 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12356 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12356 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12356 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12356 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12356,cell12356,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12356 ⟨23,by decide⟩).lower ∧ (cell12356 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12356 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12356 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12356 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12356 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12356 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12356,cell12356,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12356 ⟨24,by decide⟩).lower ∧ (cell12356 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12356 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12356 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12356 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12356 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12356 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12356,cell12356,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12356 ⟨25,by decide⟩).lower ∧ (cell12356 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12356 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12356 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12356 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12356 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12356 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12356,cell12356,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12356 ⟨26,by decide⟩).lower ∧ (cell12356 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12356 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12356 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12356 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12356 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12356 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12356,cell12356,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12356 ⟨27,by decide⟩).lower ∧ (cell12356 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12356 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12356 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12356 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12356 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12356 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12356,cell12356,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12356 ⟨28,by decide⟩).lower ∧ (cell12356 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12356 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12356 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12356 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12356 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12356 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12356,cell12356,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12356 ⟨29,by decide⟩).lower ∧ (cell12356 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12356 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12356 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12356 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12356 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12356 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12356,cell12356,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12356 ⟨30,by decide⟩).lower ∧ (cell12356 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12356 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12356 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12356 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12356 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12356 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12356,cell12356,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12356 ⟨31,by decide⟩).lower ∧ (cell12356 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12356 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12356 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12356 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12356 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12356 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12356,cell12356,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12356 ⟨32,by decide⟩).lower ∧ (cell12356 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12356 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12356 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12356 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12356 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12356 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12356,cell12356,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12356 ⟨33,by decide⟩).lower ∧ (cell12356 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12356 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12356 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12356 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12356 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12356 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12356,cell12356,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12356 ⟨34,by decide⟩).lower ∧ (cell12356 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12356 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12356 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12356 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12356 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12356 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12356,cell12356,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12356 ⟨35,by decide⟩).lower ∧ (cell12356 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12356 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12356 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12356 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12356 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12356 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12356,cell12356,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12356 ⟨36,by decide⟩).lower ∧ (cell12356 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12356 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12356 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12356 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12356 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12356 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12356,cell12356,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12356 ⟨37,by decide⟩).lower ∧ (cell12356 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12356 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12356 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12356 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12356 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12356 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12356,cell12356,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12356 ⟨38,by decide⟩).lower ∧ (cell12356 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12356 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12356 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12356 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12356 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12356 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12356,cell12356,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12356 ⟨39,by decide⟩).lower ∧ (cell12356 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12356 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12356 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12356 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12356 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12356 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12356,cell12356,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12356 ⟨40,by decide⟩).lower ∧ (cell12356 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12356 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12356 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12356 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12356 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12356 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12356,cell12356,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12356 ⟨41,by decide⟩).lower ∧ (cell12356 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12356 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12356 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12356 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12356 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12356 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12356,cell12356,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12356 ⟨42,by decide⟩).lower ∧ (cell12356 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12356 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12356 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12356 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12356 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12356 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12356,cell12356,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12356 ⟨43,by decide⟩).lower ∧ (cell12356 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12356 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12356 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12356 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12356 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12356 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12356,cell12356,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12356 ⟨44,by decide⟩).lower ∧ (cell12356 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12356 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12356 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12356 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12356 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12356 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12356,cell12356,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12356 ⟨45,by decide⟩).lower ∧ (cell12356 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12356 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12356 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12356 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12356 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12356 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12356,cell12356,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12356 ⟨46,by decide⟩).lower ∧ (cell12356 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12356 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12356 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12356 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12356 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12356 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12356,cell12356,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12356 ⟨47,by decide⟩).lower ∧ (cell12356 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12356 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12356 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12356 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12356 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12356 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12356,cell12356,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12356 ⟨48,by decide⟩).lower ∧ (cell12356 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12356 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12356 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12356 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12356 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12356 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12356,cell12356,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12356 ⟨49,by decide⟩).lower ∧ (cell12356 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12356 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12356 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12356 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12356 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12356 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12356,cell12356,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12356 ⟨50,by decide⟩).lower ∧ (cell12356 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12356 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12356 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12356 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12356 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12356 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12356,cell12356,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12356 ⟨51,by decide⟩).lower ∧ (cell12356 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12356 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12356 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12356 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12356 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12356 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12356,cell12356,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12356 ⟨52,by decide⟩).lower ∧ (cell12356 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12356 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12356 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12356 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12356 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12356 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12356,cell12356,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12356 i).lower ∧
    (cell12356 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12356 i).upper ≤ (0.532 : ℝ) ∧
    (cell12356 i).centre ≤ (0.1 : ℝ) ∧ (cell12356 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12356 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12356 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12356

/-! The local source numeric instances at 12356 have no network premises. -/
namespace BstLean.Part269.N12356
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12356)
open BstLean.Part268 (cell12356)

noncomputable def sourceNumerics12356 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12356 (cell12356 i)
      scalarRow12356.M scalarRow12356.H scalarRow12356.xi := by
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
    energy_allowance := scalarRow12356.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12356]
    centre_nonneg := (scalarRow12356.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D0.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12356])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12356
/-! Actual 12357 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12357
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12357 ≤ (1.036307208508 : ℝ) := by
  have hr : (111.162043881893 : ℝ) ≤ √(12357 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.162043881893 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12357 12357 (11 / 1000) ≤
    (0.008599042423 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12357) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.162043881893 : ℝ) ≤ √(12357 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12357)
  have hdiv : K / √(12357 : ℝ) ≤ K / 111.162043881893 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.162043881893 ≤ (0.008599042423 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12357.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12357 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12357 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12357 := gPlus_lower 12357
end BstLean.Part269.N12357

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12357
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036307208507 : ℝ) ≤ wn 12357 := by
  have hn : √(12357 : ℝ) ≤ 111.162043881894 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12357 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.162043881894 ≤ 2 / √(12357 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000258996922 : ℝ) ≤ rhoBar 12357 BstLean.Part154.csC ∧
    rhoBar 12357 BstLean.Part154.csC ≤ 0.000258997323 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036307208507 : ℝ) / (1.295212 * 12357) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036307208508 : ℝ) / (1.29521 * 12357) := by gcongr
      _ ≤ (0.000258997323 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12357 BstLean.Part154.csC) ≤ 0.001036056372 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12357 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12357 BstLean.Part154.csC) (piBar (rhoBar 12357 BstLean.Part154.csC)) ≤ 0.000197824163 ∧
    cc1 (rhoBar 12357 BstLean.Part154.csC) (piBar (rhoBar 12357 BstLean.Part154.csC)) ≤ 0.000125876775 ∧
    cc2 (rhoBar 12357 BstLean.Part154.csC) ≤ 0.000073072367 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12357 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12357 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12357 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12357 BstLean.Part154.csC * nuR (rhoBar 12357 BstLean.Part154.csC)) ≤ 0.000518011416 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000258997323 : ℝ) * 0.001036056372 := by gcongr
      _ ≤ (0.000518011416 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12357 BstLean.Part154.csC) * nuR (rhoBar 12357 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001036056372 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12357 BstLean.Part154.csC) * rhoBar 12357 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000258997323 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000258997323 / 2 + 0.399 * 0.001036056372 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000197824163 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000518011416 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125876775 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000258997323 / 1.414213562 := by gcongr
      _ ≤ (0.000073072367 : ℝ) := by norm_num

end BstLean.Part269.N12357

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12357
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12357 BstLean.Part154.csC) (piBar (rhoBar 12357 BstLean.Part154.csC)) ≤ 1.69003E-7 := by
  have hr0 : 0 ≤ rhoBar 12357 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12357 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12357 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12357 BstLean.Part154.csC) (piBar (rhoBar 12357 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12357 BstLean.Part154.csC) (piBar (rhoBar 12357 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12357 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000197824163 : ℝ) ^ 2 + 0.000125876775 ^ 2 + 3 * 0.000073072367 ^ 2 +
        2 * 0.797885 * 0.000197824163 * 0.000125876775 + 2 * 0.000197824163 * 0.000073072367 +
        4 * 0.797885 * 0.000125876775 * 0.000073072367 := by gcongr
    _ ≤ (1.69003E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12357 BstLean.Part154.csC Θ ≤ 0.002704881986 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12357 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12357 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12357 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12357 BstLean.Part154.csC) (piBar (rhoBar 12357 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12357 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036307208508 * 1.69003E-7 / (0.000258996922 : ℝ) := by gcongr
    _ ≤ 0.002704881986 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12357 BstLean.Part154.csC Θ ≤ 0.003002648084 + 0.000683477149 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12357 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12357 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12357 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036307208508 : ℝ) * ((2 * Θ * 0.000258997323 +
        (6863 / 10000) * 0.000258997323 * 12357 * 0.001036056372) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003002648084 + 0.000683477149 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12357 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12357 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12357 0.011 Θ ∧ gammaRatio 12357 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12357 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036307208508 : ℝ) * 0.525 / ((1 - 0.011) * 12357) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12357 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12357 0.011 Θ) :=
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
    badAllowance 12357 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12357 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12357 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12357 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12357 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12357 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12357 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12357 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12357 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12357 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12357 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036307208508 : ℝ) * 12357 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12357 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004102648084 + 0.003388359135 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12357

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12357
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12357 BstLean.Part154.csC) (piBar (rhoBar 12357 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12357 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12357 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12357 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12357 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12357 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12357 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12357 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12357 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12357 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12357 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12357 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12357 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12357 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12357 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053215697492 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12357) ≤ 0.010743213595 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12357 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036307208508)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010743213595 + 2 * 0.737676 / 12357) := by gcongr
    _ ≤ (0.053215697492 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12357 12 ≤ 0.0015 := by
  exact BstLean.Part269.S0.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12357

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12357
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560487626252 : ℝ) ≤ plow 12357 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12357) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053388136630)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001420063043) : eMP 12357 0.011 xi bn ≤ 0.001222105737 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12357 : ℝ) * (1 - 0.011))) ≤ 0.000604190795 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001420063043 / (12357 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000604190795 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000604190795 : ℝ) + 3.141593 * 0.053388136630 / (12357 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001222105737 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053388136630)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001420063043) : PiBarMP 12357 12 0.011 xi bn ≤ 0.163498337603 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12357 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037683723848 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.548962003268 : ℝ) ≤ √((12357 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.162043881893 : ℝ) ≤ √(12357 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12357) ≤ 0.125334221793 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037683723848 + 0.053388136630 * 1.772454 / (2 * (110.548962003268 : ℝ))) * (1 + 0.001222105737) +
        8 / (12357 * 111.162043881893) + 0.125334221793 := by gcongr
    _ ≤ (0.163498337603 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053388136630)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001420063043) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284274427321) :
    parallelOracle 12357 0.011 xi bn cd ≤ 0.164519848303 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12357 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12357 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560487626252 : ℝ) ≤ plow 12357 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.162043881893 : ℝ) ≤ √(12357 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284274427321 : ℝ) / (2 * 0.560487626252 * 111.162043881893)) * 0.163498337603 +
        0.284274427321 ^ 2 / (2 * 0.560487626252 * 111.162043881893) := by gcongr
    _ ≤ (0.164519848303 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053388136630) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001420063043)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284274427321) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12357 12357 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560487626252 : ℝ) ≤ plow 12357 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.162043881893 : ℝ) ≤ √(12357 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12357 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12357 Θ 1.22 ≤ 0.011929436107 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.162043881893 := by gcongr <;> linarith
      _ ≤ (0.011929436107 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12357 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12357 12357 0.011 ≤ 0.008599042423 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12357 12357 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12357 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12357 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12357 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12357 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164519848303 + 0.011929436107 + (0.008599042423 : ℝ) *
        (1 + 2 * (0.284274427321 + 0.011929436107) / (0.560487626252 * 111.162043881893))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12357]

end BstLean.Part269.N12357

/-! The original eight local profiles supply actual 12357 moment certificates. -/
namespace BstLean.Part269.N12357
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12357 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12357 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12357 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053388136630 ∧
    0 ≤ bN 12357 BstLean.Part154.csC (groupTheta g) ∧ bN 12357 BstLean.Part154.csC (groupTheta g) ≤ 0.001420063043 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12357 12357 0.011
      (momentAllowance 12357 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12357 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12357 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12357 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12357 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12357 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231058729829 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12357 0.011
      (momentAllowance 12357 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12357 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12357
/-! The actual computed-centre upper energy formula at 12357. -/
namespace BstLean.Part269.N12357
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12357

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12357
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12357)
open BstLean.Part268 (cell12357)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086562589877
  | 2 => 0.087526771527
  | 3 => 0.088492489540
  | 4 => 0.089461922690
  | 5 => 0.090437677415
  | 6 => 0.091422847459
  | 7 => 0.092421078426
  | 8 => 0.093436637196
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12357 12357 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12357 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004104440387 + 0.003390347157 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S0.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12357

/-! Actual upper energy certificates on all 43 source endpoints at 12357. -/
namespace BstLean.Part269.N12357
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12357)
open BstLean.Part268 (cell12357)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12357 (gMinus 12357) (1 - (cell12357 i).lower) ≤ 1 ∧
    energyUpper 12357 (gMinus 12357) (BstLean.Part211.gPlus 12357)
      (finiteEnergy 12357 12357 0.011) (1 - (cell12357 i).lower) ≤
      (cell12357 i).energy := by
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
      have E := BstLean.Part269.S0.uniformEnergy10 (n := 12357) (by norm_num)
        (q := 1 - (cell12357 ⟨10,by decide⟩).lower)
        (by norm_num [cell12357]) (by norm_num [cell12357])
      exact ⟨E.1,E.2.trans (by norm_num [cell12357])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy11 (n := 12357) (by norm_num)
        (q := 1 - (cell12357 ⟨11,by decide⟩).lower)
        (by norm_num [cell12357]) (by norm_num [cell12357])
      exact ⟨E.1,E.2.trans (by norm_num [cell12357])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy12 (n := 12357) (by norm_num)
        (q := 1 - (cell12357 ⟨12,by decide⟩).lower)
        (by norm_num [cell12357]) (by norm_num [cell12357])
      exact ⟨E.1,E.2.trans (by norm_num [cell12357])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy13 (n := 12357) (by norm_num)
        (q := 1 - (cell12357 ⟨13,by decide⟩).lower)
        (by norm_num [cell12357]) (by norm_num [cell12357])
      exact ⟨E.1,E.2.trans (by norm_num [cell12357])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy14 (n := 12357) (by norm_num)
        (q := 1 - (cell12357 ⟨14,by decide⟩).lower)
        (by norm_num [cell12357]) (by norm_num [cell12357])
      exact ⟨E.1,E.2.trans (by norm_num [cell12357])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy15 (n := 12357) (by norm_num)
        (q := 1 - (cell12357 ⟨15,by decide⟩).lower)
        (by norm_num [cell12357]) (by norm_num [cell12357])
      exact ⟨E.1,E.2.trans (by norm_num [cell12357])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy16 (n := 12357) (by norm_num)
        (q := 1 - (cell12357 ⟨16,by decide⟩).lower)
        (by norm_num [cell12357]) (by norm_num [cell12357])
      exact ⟨E.1,E.2.trans (by norm_num [cell12357])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy17 (n := 12357) (by norm_num)
        (q := 1 - (cell12357 ⟨17,by decide⟩).lower)
        (by norm_num [cell12357]) (by norm_num [cell12357])
      exact ⟨E.1,E.2.trans (by norm_num [cell12357])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy18 (n := 12357) (by norm_num)
        (q := 1 - (cell12357 ⟨18,by decide⟩).lower)
        (by norm_num [cell12357]) (by norm_num [cell12357])
      exact ⟨E.1,E.2.trans (by norm_num [cell12357])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy19 (n := 12357) (by norm_num)
        (q := 1 - (cell12357 ⟨19,by decide⟩).lower)
        (by norm_num [cell12357]) (by norm_num [cell12357])
      exact ⟨E.1,E.2.trans (by norm_num [cell12357])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy20 (n := 12357) (by norm_num)
        (q := 1 - (cell12357 ⟨20,by decide⟩).lower)
        (by norm_num [cell12357]) (by norm_num [cell12357])
      exact ⟨E.1,E.2.trans (by norm_num [cell12357])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy21 (n := 12357) (by norm_num)
        (q := 1 - (cell12357 ⟨21,by decide⟩).lower)
        (by norm_num [cell12357]) (by norm_num [cell12357])
      exact ⟨E.1,E.2.trans (by norm_num [cell12357])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy22 (n := 12357) (by norm_num)
        (q := 1 - (cell12357 ⟨22,by decide⟩).lower)
        (by norm_num [cell12357]) (by norm_num [cell12357])
      exact ⟨E.1,E.2.trans (by norm_num [cell12357])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy23 (n := 12357) (by norm_num)
        (q := 1 - (cell12357 ⟨23,by decide⟩).lower)
        (by norm_num [cell12357]) (by norm_num [cell12357])
      exact ⟨E.1,E.2.trans (by norm_num [cell12357])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy24 (n := 12357) (by norm_num)
        (q := 1 - (cell12357 ⟨24,by decide⟩).lower)
        (by norm_num [cell12357]) (by norm_num [cell12357])
      exact ⟨E.1,E.2.trans (by norm_num [cell12357])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy25 (n := 12357) (by norm_num)
        (q := 1 - (cell12357 ⟨25,by decide⟩).lower)
        (by norm_num [cell12357]) (by norm_num [cell12357])
      exact ⟨E.1,E.2.trans (by norm_num [cell12357])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy26 (n := 12357) (by norm_num)
        (q := 1 - (cell12357 ⟨26,by decide⟩).lower)
        (by norm_num [cell12357]) (by norm_num [cell12357])
      exact ⟨E.1,E.2.trans (by norm_num [cell12357])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy27 (n := 12357) (by norm_num)
        (q := 1 - (cell12357 ⟨27,by decide⟩).lower)
        (by norm_num [cell12357]) (by norm_num [cell12357])
      exact ⟨E.1,E.2.trans (by norm_num [cell12357])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy28 (n := 12357) (by norm_num)
        (q := 1 - (cell12357 ⟨28,by decide⟩).lower)
        (by norm_num [cell12357]) (by norm_num [cell12357])
      exact ⟨E.1,E.2.trans (by norm_num [cell12357])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy29 (n := 12357) (by norm_num)
        (q := 1 - (cell12357 ⟨29,by decide⟩).lower)
        (by norm_num [cell12357]) (by norm_num [cell12357])
      exact ⟨E.1,E.2.trans (by norm_num [cell12357])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy30 (n := 12357) (by norm_num)
        (q := 1 - (cell12357 ⟨30,by decide⟩).lower)
        (by norm_num [cell12357]) (by norm_num [cell12357])
      exact ⟨E.1,E.2.trans (by norm_num [cell12357])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy31 (n := 12357) (by norm_num)
        (q := 1 - (cell12357 ⟨31,by decide⟩).lower)
        (by norm_num [cell12357]) (by norm_num [cell12357])
      exact ⟨E.1,E.2.trans (by norm_num [cell12357])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy32 (n := 12357) (by norm_num)
        (q := 1 - (cell12357 ⟨32,by decide⟩).lower)
        (by norm_num [cell12357]) (by norm_num [cell12357])
      exact ⟨E.1,E.2.trans (by norm_num [cell12357])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy33 (n := 12357) (by norm_num)
        (q := 1 - (cell12357 ⟨33,by decide⟩).lower)
        (by norm_num [cell12357]) (by norm_num [cell12357])
      exact ⟨E.1,E.2.trans (by norm_num [cell12357])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy34 (n := 12357) (by norm_num)
        (q := 1 - (cell12357 ⟨34,by decide⟩).lower)
        (by norm_num [cell12357]) (by norm_num [cell12357])
      exact ⟨E.1,E.2.trans (by norm_num [cell12357])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy35 (n := 12357) (by norm_num)
        (q := 1 - (cell12357 ⟨35,by decide⟩).lower)
        (by norm_num [cell12357]) (by norm_num [cell12357])
      exact ⟨E.1,E.2.trans (by norm_num [cell12357])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy36 (n := 12357) (by norm_num)
        (q := 1 - (cell12357 ⟨36,by decide⟩).lower)
        (by norm_num [cell12357]) (by norm_num [cell12357])
      exact ⟨E.1,E.2.trans (by norm_num [cell12357])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy37 (n := 12357) (by norm_num)
        (q := 1 - (cell12357 ⟨37,by decide⟩).lower)
        (by norm_num [cell12357]) (by norm_num [cell12357])
      exact ⟨E.1,E.2.trans (by norm_num [cell12357])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy38 (n := 12357) (by norm_num)
        (q := 1 - (cell12357 ⟨38,by decide⟩).lower)
        (by norm_num [cell12357]) (by norm_num [cell12357])
      exact ⟨E.1,E.2.trans (by norm_num [cell12357])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy39 (n := 12357) (by norm_num)
        (q := 1 - (cell12357 ⟨39,by decide⟩).lower)
        (by norm_num [cell12357]) (by norm_num [cell12357])
      exact ⟨E.1,E.2.trans (by norm_num [cell12357])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy40 (n := 12357) (by norm_num)
        (q := 1 - (cell12357 ⟨40,by decide⟩).lower)
        (by norm_num [cell12357]) (by norm_num [cell12357])
      exact ⟨E.1,E.2.trans (by norm_num [cell12357])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy41 (n := 12357) (by norm_num)
        (q := 1 - (cell12357 ⟨41,by decide⟩).lower)
        (by norm_num [cell12357]) (by norm_num [cell12357])
      exact ⟨E.1,E.2.trans (by norm_num [cell12357])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy42 (n := 12357) (by norm_num)
        (q := 1 - (cell12357 ⟨42,by decide⟩).lower)
        (by norm_num [cell12357]) (by norm_num [cell12357])
      exact ⟨E.1,E.2.trans (by norm_num [cell12357])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy43 (n := 12357) (by norm_num)
        (q := 1 - (cell12357 ⟨43,by decide⟩).lower)
        (by norm_num [cell12357]) (by norm_num [cell12357])
      exact ⟨E.1,E.2.trans (by norm_num [cell12357])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy44 (n := 12357) (by norm_num)
        (q := 1 - (cell12357 ⟨44,by decide⟩).lower)
        (by norm_num [cell12357]) (by norm_num [cell12357])
      exact ⟨E.1,E.2.trans (by norm_num [cell12357])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy45 (n := 12357) (by norm_num)
        (q := 1 - (cell12357 ⟨45,by decide⟩).lower)
        (by norm_num [cell12357]) (by norm_num [cell12357])
      exact ⟨E.1,E.2.trans (by norm_num [cell12357])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy46 (n := 12357) (by norm_num)
        (q := 1 - (cell12357 ⟨46,by decide⟩).lower)
        (by norm_num [cell12357]) (by norm_num [cell12357])
      exact ⟨E.1,E.2.trans (by norm_num [cell12357])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy47 (n := 12357) (by norm_num)
        (q := 1 - (cell12357 ⟨47,by decide⟩).lower)
        (by norm_num [cell12357]) (by norm_num [cell12357])
      exact ⟨E.1,E.2.trans (by norm_num [cell12357])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy48 (n := 12357) (by norm_num)
        (q := 1 - (cell12357 ⟨48,by decide⟩).lower)
        (by norm_num [cell12357]) (by norm_num [cell12357])
      exact ⟨E.1,E.2.trans (by norm_num [cell12357])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy49 (n := 12357) (by norm_num)
        (q := 1 - (cell12357 ⟨49,by decide⟩).lower)
        (by norm_num [cell12357]) (by norm_num [cell12357])
      exact ⟨E.1,E.2.trans (by norm_num [cell12357])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy50 (n := 12357) (by norm_num)
        (q := 1 - (cell12357 ⟨50,by decide⟩).lower)
        (by norm_num [cell12357]) (by norm_num [cell12357])
      exact ⟨E.1,E.2.trans (by norm_num [cell12357])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy51 (n := 12357) (by norm_num)
        (q := 1 - (cell12357 ⟨51,by decide⟩).lower)
        (by norm_num [cell12357]) (by norm_num [cell12357])
      exact ⟨E.1,E.2.trans (by norm_num [cell12357])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy52 (n := 12357) (by norm_num)
        (q := 1 - (cell12357 ⟨52,by decide⟩).lower)
        (by norm_num [cell12357]) (by norm_num [cell12357])
      exact ⟨E.1,E.2.trans (by norm_num [cell12357])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12357

/-! Source-cell containment and simple scalar guards at 12357. -/
namespace BstLean.Part269.N12357
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12357)
open BstLean.Part268 (cell12357)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12357 ⟨10,by decide⟩).lower ∧ (cell12357 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12357 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12357 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12357 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12357 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12357 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12357,cell12357,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12357 ⟨11,by decide⟩).lower ∧ (cell12357 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12357 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12357 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12357 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12357 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12357 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12357,cell12357,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12357 ⟨12,by decide⟩).lower ∧ (cell12357 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12357 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12357 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12357 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12357 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12357 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12357,cell12357,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12357 ⟨13,by decide⟩).lower ∧ (cell12357 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12357 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12357 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12357 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12357 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12357 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12357,cell12357,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12357 ⟨14,by decide⟩).lower ∧ (cell12357 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12357 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12357 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12357 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12357 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12357 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12357,cell12357,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12357 ⟨15,by decide⟩).lower ∧ (cell12357 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12357 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12357 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12357 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12357 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12357 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12357,cell12357,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12357 ⟨16,by decide⟩).lower ∧ (cell12357 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12357 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12357 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12357 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12357 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12357 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12357,cell12357,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12357 ⟨17,by decide⟩).lower ∧ (cell12357 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12357 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12357 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12357 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12357 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12357 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12357,cell12357,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12357 ⟨18,by decide⟩).lower ∧ (cell12357 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12357 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12357 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12357 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12357 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12357 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12357,cell12357,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12357 ⟨19,by decide⟩).lower ∧ (cell12357 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12357 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12357 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12357 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12357 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12357 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12357,cell12357,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12357 ⟨20,by decide⟩).lower ∧ (cell12357 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12357 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12357 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12357 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12357 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12357 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12357,cell12357,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12357 ⟨21,by decide⟩).lower ∧ (cell12357 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12357 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12357 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12357 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12357 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12357 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12357,cell12357,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12357 ⟨22,by decide⟩).lower ∧ (cell12357 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12357 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12357 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12357 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12357 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12357 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12357,cell12357,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12357 ⟨23,by decide⟩).lower ∧ (cell12357 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12357 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12357 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12357 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12357 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12357 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12357,cell12357,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12357 ⟨24,by decide⟩).lower ∧ (cell12357 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12357 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12357 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12357 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12357 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12357 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12357,cell12357,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12357 ⟨25,by decide⟩).lower ∧ (cell12357 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12357 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12357 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12357 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12357 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12357 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12357,cell12357,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12357 ⟨26,by decide⟩).lower ∧ (cell12357 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12357 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12357 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12357 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12357 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12357 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12357,cell12357,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12357 ⟨27,by decide⟩).lower ∧ (cell12357 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12357 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12357 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12357 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12357 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12357 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12357,cell12357,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12357 ⟨28,by decide⟩).lower ∧ (cell12357 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12357 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12357 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12357 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12357 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12357 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12357,cell12357,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12357 ⟨29,by decide⟩).lower ∧ (cell12357 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12357 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12357 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12357 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12357 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12357 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12357,cell12357,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12357 ⟨30,by decide⟩).lower ∧ (cell12357 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12357 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12357 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12357 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12357 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12357 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12357,cell12357,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12357 ⟨31,by decide⟩).lower ∧ (cell12357 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12357 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12357 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12357 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12357 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12357 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12357,cell12357,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12357 ⟨32,by decide⟩).lower ∧ (cell12357 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12357 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12357 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12357 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12357 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12357 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12357,cell12357,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12357 ⟨33,by decide⟩).lower ∧ (cell12357 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12357 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12357 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12357 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12357 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12357 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12357,cell12357,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12357 ⟨34,by decide⟩).lower ∧ (cell12357 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12357 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12357 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12357 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12357 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12357 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12357,cell12357,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12357 ⟨35,by decide⟩).lower ∧ (cell12357 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12357 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12357 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12357 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12357 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12357 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12357,cell12357,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12357 ⟨36,by decide⟩).lower ∧ (cell12357 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12357 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12357 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12357 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12357 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12357 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12357,cell12357,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12357 ⟨37,by decide⟩).lower ∧ (cell12357 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12357 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12357 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12357 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12357 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12357 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12357,cell12357,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12357 ⟨38,by decide⟩).lower ∧ (cell12357 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12357 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12357 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12357 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12357 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12357 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12357,cell12357,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12357 ⟨39,by decide⟩).lower ∧ (cell12357 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12357 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12357 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12357 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12357 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12357 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12357,cell12357,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12357 ⟨40,by decide⟩).lower ∧ (cell12357 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12357 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12357 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12357 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12357 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12357 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12357,cell12357,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12357 ⟨41,by decide⟩).lower ∧ (cell12357 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12357 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12357 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12357 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12357 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12357 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12357,cell12357,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12357 ⟨42,by decide⟩).lower ∧ (cell12357 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12357 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12357 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12357 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12357 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12357 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12357,cell12357,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12357 ⟨43,by decide⟩).lower ∧ (cell12357 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12357 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12357 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12357 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12357 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12357 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12357,cell12357,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12357 ⟨44,by decide⟩).lower ∧ (cell12357 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12357 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12357 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12357 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12357 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12357 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12357,cell12357,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12357 ⟨45,by decide⟩).lower ∧ (cell12357 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12357 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12357 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12357 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12357 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12357 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12357,cell12357,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12357 ⟨46,by decide⟩).lower ∧ (cell12357 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12357 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12357 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12357 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12357 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12357 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12357,cell12357,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12357 ⟨47,by decide⟩).lower ∧ (cell12357 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12357 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12357 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12357 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12357 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12357 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12357,cell12357,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12357 ⟨48,by decide⟩).lower ∧ (cell12357 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12357 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12357 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12357 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12357 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12357 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12357,cell12357,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12357 ⟨49,by decide⟩).lower ∧ (cell12357 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12357 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12357 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12357 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12357 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12357 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12357,cell12357,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12357 ⟨50,by decide⟩).lower ∧ (cell12357 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12357 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12357 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12357 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12357 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12357 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12357,cell12357,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12357 ⟨51,by decide⟩).lower ∧ (cell12357 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12357 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12357 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12357 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12357 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12357 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12357,cell12357,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12357 ⟨52,by decide⟩).lower ∧ (cell12357 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12357 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12357 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12357 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12357 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12357 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12357,cell12357,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12357 i).lower ∧
    (cell12357 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12357 i).upper ≤ (0.532 : ℝ) ∧
    (cell12357 i).centre ≤ (0.1 : ℝ) ∧ (cell12357 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12357 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12357 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12357

/-! The local source numeric instances at 12357 have no network premises. -/
namespace BstLean.Part269.N12357
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12357)
open BstLean.Part268 (cell12357)

noncomputable def sourceNumerics12357 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12357 (cell12357 i)
      scalarRow12357.M scalarRow12357.H scalarRow12357.xi := by
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
    energy_allowance := scalarRow12357.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12357]
    centre_nonneg := (scalarRow12357.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D0.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12357])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12357
/-! Actual 12358 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12358
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12358 ≤ (1.036305726406 : ℝ) := by
  have hr : (111.166541729065 : ℝ) ≤ √(12358 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.166541729065 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12358 12358 (11 / 1000) ≤
    (0.008598694499 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12358) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.166541729065 : ℝ) ≤ √(12358 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12358)
  have hdiv : K / √(12358 : ℝ) ≤ K / 111.166541729065 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.166541729065 ≤ (0.008598694499 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12358.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12358 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12358 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12358 := gPlus_lower 12358
end BstLean.Part269.N12358

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12358
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036305726405 : ℝ) ≤ wn 12358 := by
  have hn : √(12358 : ℝ) ≤ 111.166541729066 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12358 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.166541729066 ≤ 2 / √(12358 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000258975594 : ℝ) ≤ rhoBar 12358 BstLean.Part154.csC ∧
    rhoBar 12358 BstLean.Part154.csC ≤ 0.000258975995 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036305726405 : ℝ) / (1.295212 * 12358) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036305726406 : ℝ) / (1.29521 * 12358) := by gcongr
      _ ≤ (0.000258975995 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12358 BstLean.Part154.csC) ≤ 0.001035971049 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12358 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12358 BstLean.Part154.csC) (piBar (rhoBar 12358 BstLean.Part154.csC)) ≤ 0.000197807871 ∧
    cc1 (rhoBar 12358 BstLean.Part154.csC) (piBar (rhoBar 12358 BstLean.Part154.csC)) ≤ 0.000125866408 ∧
    cc2 (rhoBar 12358 BstLean.Part154.csC) ≤ 0.000073066350 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12358 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12358 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12358 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12358 BstLean.Part154.csC * nuR (rhoBar 12358 BstLean.Part154.csC)) ≤ 0.000517968757 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000258975995 : ℝ) * 0.001035971049 := by gcongr
      _ ≤ (0.000517968757 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12358 BstLean.Part154.csC) * nuR (rhoBar 12358 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001035971049 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12358 BstLean.Part154.csC) * rhoBar 12358 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000258975995 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000258975995 / 2 + 0.399 * 0.001035971049 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000197807871 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000517968757 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125866408 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000258975995 / 1.414213562 := by gcongr
      _ ≤ (0.000073066350 : ℝ) := by norm_num

end BstLean.Part269.N12358

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12358
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12358 BstLean.Part154.csC) (piBar (rhoBar 12358 BstLean.Part154.csC)) ≤ 1.68975E-7 := by
  have hr0 : 0 ≤ rhoBar 12358 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12358 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12358 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12358 BstLean.Part154.csC) (piBar (rhoBar 12358 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12358 BstLean.Part154.csC) (piBar (rhoBar 12358 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12358 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000197807871 : ℝ) ^ 2 + 0.000125866408 ^ 2 + 3 * 0.000073066350 ^ 2 +
        2 * 0.797885 * 0.000197807871 * 0.000125866408 + 2 * 0.000197807871 * 0.000073066350 +
        4 * 0.797885 * 0.000125866408 * 0.000073066350 := by gcongr
    _ ≤ (1.68975E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12358 BstLean.Part154.csC Θ ≤ 0.002704652704 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12358 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12358 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12358 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12358 BstLean.Part154.csC) (piBar (rhoBar 12358 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12358 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036305726406 * 1.68975E-7 / (0.000258975594 : ℝ) := by gcongr
    _ ≤ 0.002704652704 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12358 BstLean.Part154.csC Θ ≤ 0.003002392220 + 0.000683419889 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12358 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12358 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12358 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036305726406 : ℝ) * ((2 * Θ * 0.000258975995 +
        (6863 / 10000) * 0.000258975995 * 12358 * 0.001035971049) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003002392220 + 0.000683419889 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12358 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12358 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12358 0.011 Θ ∧ gammaRatio 12358 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12358 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036305726406 : ℝ) * 0.525 / ((1 - 0.011) * 12358) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12358 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12358 0.011 Θ) :=
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
    badAllowance 12358 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12358 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12358 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12358 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12358 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12358 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12358 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12358 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12358 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12358 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12358 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036305726406 : ℝ) * 12358 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12358 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004102392220 + 0.003388072593 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12358

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12358
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12358 BstLean.Part154.csC) (piBar (rhoBar 12358 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12358 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12358 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12358 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12358 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12358 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12358 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12358 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12358 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12358 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12358 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12358 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12358 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12358 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12358 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053213520697 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12358) ≤ 0.010742778920 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12358 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036305726406)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010742778920 + 2 * 0.737676 / 12358) := by gcongr
    _ ≤ (0.053213520697 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12358 12 ≤ 0.0015 := by
  exact BstLean.Part269.S0.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12358

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12358
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560487674016 : ℝ) ≤ plow 12358 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12358) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053387730332)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001419942670) : eMP 12358 0.011 xi bn ≤ 0.001222004416 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12358 : ℝ) * (1 - 0.011))) ≤ 0.000604140742 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001419942670 / (12358 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000604140742 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000604140742 : ℝ) + 3.141593 * 0.053387730332 / (12358 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001222004416 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053387730332)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001419942670) : PiBarMP 12358 12 0.011 xi bn ≤ 0.163491642224 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12358 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037682126666 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.553435043873 : ℝ) ≤ √((12358 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.166541729065 : ℝ) ≤ √(12358 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12358) ≤ 0.125329150715 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037682126666 + 0.053387730332 * 1.772454 / (2 * (110.553435043873 : ℝ))) * (1 + 0.001222004416) +
        8 / (12358 * 111.166541729065) + 0.125329150715 := by gcongr
    _ ≤ (0.163491642224 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053387730332)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001419942670) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284271371315) :
    parallelOracle 12358 0.011 xi bn cd ≤ 0.164513078280 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12358 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12358 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560487674016 : ℝ) ≤ plow 12358 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.166541729065 : ℝ) ≤ √(12358 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284271371315 : ℝ) / (2 * 0.560487674016 * 111.166541729065)) * 0.163491642224 +
        0.284271371315 ^ 2 / (2 * 0.560487674016 * 111.166541729065) := by gcongr
    _ ≤ (0.164513078280 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053387730332) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001419942670)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284271371315) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12358 12358 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560487674016 : ℝ) ≤ plow 12358 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.166541729065 : ℝ) ≤ √(12358 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12358 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12358 Θ 1.22 ≤ 0.011928953437 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.166541729065 := by gcongr <;> linarith
      _ ≤ (0.011928953437 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12358 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12358 12358 0.011 ≤ 0.008598694499 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12358 12358 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12358 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12358 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12358 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12358 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164513078280 + 0.011928953437 + (0.008598694499 : ℝ) *
        (1 + 2 * (0.284271371315 + 0.011928953437) / (0.560487674016 * 111.166541729065))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12358]

end BstLean.Part269.N12358

/-! The original eight local profiles supply actual 12358 moment certificates. -/
namespace BstLean.Part269.N12358
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12358 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12358 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12358 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053387730332 ∧
    0 ≤ bN 12358 BstLean.Part154.csC (groupTheta g) ∧ bN 12358 BstLean.Part154.csC (groupTheta g) ≤ 0.001419942670 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12358 12358 0.011
      (momentAllowance 12358 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12358 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12358 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12358 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12358 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12358 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231057850618 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12358 0.011
      (momentAllowance 12358 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12358 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12358
/-! The actual computed-centre upper energy formula at 12358. -/
namespace BstLean.Part269.N12358
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12358

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12358
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12358)
open BstLean.Part268 (cell12358)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086559227256
  | 2 => 0.087523336114
  | 3 => 0.088488969025
  | 4 => 0.089458302074
  | 5 => 0.090433938557
  | 6 => 0.091418968574
  | 7 => 0.092417033535
  | 8 => 0.093432395512
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12358 12358 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12358 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004104440387 + 0.003390347157 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S0.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12358

/-! Actual upper energy certificates on all 43 source endpoints at 12358. -/
namespace BstLean.Part269.N12358
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12358)
open BstLean.Part268 (cell12358)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12358 (gMinus 12358) (1 - (cell12358 i).lower) ≤ 1 ∧
    energyUpper 12358 (gMinus 12358) (BstLean.Part211.gPlus 12358)
      (finiteEnergy 12358 12358 0.011) (1 - (cell12358 i).lower) ≤
      (cell12358 i).energy := by
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
      have E := BstLean.Part269.S0.uniformEnergy10 (n := 12358) (by norm_num)
        (q := 1 - (cell12358 ⟨10,by decide⟩).lower)
        (by norm_num [cell12358]) (by norm_num [cell12358])
      exact ⟨E.1,E.2.trans (by norm_num [cell12358])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy11 (n := 12358) (by norm_num)
        (q := 1 - (cell12358 ⟨11,by decide⟩).lower)
        (by norm_num [cell12358]) (by norm_num [cell12358])
      exact ⟨E.1,E.2.trans (by norm_num [cell12358])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy12 (n := 12358) (by norm_num)
        (q := 1 - (cell12358 ⟨12,by decide⟩).lower)
        (by norm_num [cell12358]) (by norm_num [cell12358])
      exact ⟨E.1,E.2.trans (by norm_num [cell12358])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy13 (n := 12358) (by norm_num)
        (q := 1 - (cell12358 ⟨13,by decide⟩).lower)
        (by norm_num [cell12358]) (by norm_num [cell12358])
      exact ⟨E.1,E.2.trans (by norm_num [cell12358])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy14 (n := 12358) (by norm_num)
        (q := 1 - (cell12358 ⟨14,by decide⟩).lower)
        (by norm_num [cell12358]) (by norm_num [cell12358])
      exact ⟨E.1,E.2.trans (by norm_num [cell12358])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy15 (n := 12358) (by norm_num)
        (q := 1 - (cell12358 ⟨15,by decide⟩).lower)
        (by norm_num [cell12358]) (by norm_num [cell12358])
      exact ⟨E.1,E.2.trans (by norm_num [cell12358])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy16 (n := 12358) (by norm_num)
        (q := 1 - (cell12358 ⟨16,by decide⟩).lower)
        (by norm_num [cell12358]) (by norm_num [cell12358])
      exact ⟨E.1,E.2.trans (by norm_num [cell12358])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy17 (n := 12358) (by norm_num)
        (q := 1 - (cell12358 ⟨17,by decide⟩).lower)
        (by norm_num [cell12358]) (by norm_num [cell12358])
      exact ⟨E.1,E.2.trans (by norm_num [cell12358])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy18 (n := 12358) (by norm_num)
        (q := 1 - (cell12358 ⟨18,by decide⟩).lower)
        (by norm_num [cell12358]) (by norm_num [cell12358])
      exact ⟨E.1,E.2.trans (by norm_num [cell12358])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy19 (n := 12358) (by norm_num)
        (q := 1 - (cell12358 ⟨19,by decide⟩).lower)
        (by norm_num [cell12358]) (by norm_num [cell12358])
      exact ⟨E.1,E.2.trans (by norm_num [cell12358])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy20 (n := 12358) (by norm_num)
        (q := 1 - (cell12358 ⟨20,by decide⟩).lower)
        (by norm_num [cell12358]) (by norm_num [cell12358])
      exact ⟨E.1,E.2.trans (by norm_num [cell12358])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy21 (n := 12358) (by norm_num)
        (q := 1 - (cell12358 ⟨21,by decide⟩).lower)
        (by norm_num [cell12358]) (by norm_num [cell12358])
      exact ⟨E.1,E.2.trans (by norm_num [cell12358])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy22 (n := 12358) (by norm_num)
        (q := 1 - (cell12358 ⟨22,by decide⟩).lower)
        (by norm_num [cell12358]) (by norm_num [cell12358])
      exact ⟨E.1,E.2.trans (by norm_num [cell12358])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy23 (n := 12358) (by norm_num)
        (q := 1 - (cell12358 ⟨23,by decide⟩).lower)
        (by norm_num [cell12358]) (by norm_num [cell12358])
      exact ⟨E.1,E.2.trans (by norm_num [cell12358])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy24 (n := 12358) (by norm_num)
        (q := 1 - (cell12358 ⟨24,by decide⟩).lower)
        (by norm_num [cell12358]) (by norm_num [cell12358])
      exact ⟨E.1,E.2.trans (by norm_num [cell12358])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy25 (n := 12358) (by norm_num)
        (q := 1 - (cell12358 ⟨25,by decide⟩).lower)
        (by norm_num [cell12358]) (by norm_num [cell12358])
      exact ⟨E.1,E.2.trans (by norm_num [cell12358])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy26 (n := 12358) (by norm_num)
        (q := 1 - (cell12358 ⟨26,by decide⟩).lower)
        (by norm_num [cell12358]) (by norm_num [cell12358])
      exact ⟨E.1,E.2.trans (by norm_num [cell12358])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy27 (n := 12358) (by norm_num)
        (q := 1 - (cell12358 ⟨27,by decide⟩).lower)
        (by norm_num [cell12358]) (by norm_num [cell12358])
      exact ⟨E.1,E.2.trans (by norm_num [cell12358])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy28 (n := 12358) (by norm_num)
        (q := 1 - (cell12358 ⟨28,by decide⟩).lower)
        (by norm_num [cell12358]) (by norm_num [cell12358])
      exact ⟨E.1,E.2.trans (by norm_num [cell12358])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy29 (n := 12358) (by norm_num)
        (q := 1 - (cell12358 ⟨29,by decide⟩).lower)
        (by norm_num [cell12358]) (by norm_num [cell12358])
      exact ⟨E.1,E.2.trans (by norm_num [cell12358])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy30 (n := 12358) (by norm_num)
        (q := 1 - (cell12358 ⟨30,by decide⟩).lower)
        (by norm_num [cell12358]) (by norm_num [cell12358])
      exact ⟨E.1,E.2.trans (by norm_num [cell12358])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy31 (n := 12358) (by norm_num)
        (q := 1 - (cell12358 ⟨31,by decide⟩).lower)
        (by norm_num [cell12358]) (by norm_num [cell12358])
      exact ⟨E.1,E.2.trans (by norm_num [cell12358])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy32 (n := 12358) (by norm_num)
        (q := 1 - (cell12358 ⟨32,by decide⟩).lower)
        (by norm_num [cell12358]) (by norm_num [cell12358])
      exact ⟨E.1,E.2.trans (by norm_num [cell12358])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy33 (n := 12358) (by norm_num)
        (q := 1 - (cell12358 ⟨33,by decide⟩).lower)
        (by norm_num [cell12358]) (by norm_num [cell12358])
      exact ⟨E.1,E.2.trans (by norm_num [cell12358])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy34 (n := 12358) (by norm_num)
        (q := 1 - (cell12358 ⟨34,by decide⟩).lower)
        (by norm_num [cell12358]) (by norm_num [cell12358])
      exact ⟨E.1,E.2.trans (by norm_num [cell12358])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy35 (n := 12358) (by norm_num)
        (q := 1 - (cell12358 ⟨35,by decide⟩).lower)
        (by norm_num [cell12358]) (by norm_num [cell12358])
      exact ⟨E.1,E.2.trans (by norm_num [cell12358])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy36 (n := 12358) (by norm_num)
        (q := 1 - (cell12358 ⟨36,by decide⟩).lower)
        (by norm_num [cell12358]) (by norm_num [cell12358])
      exact ⟨E.1,E.2.trans (by norm_num [cell12358])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy37 (n := 12358) (by norm_num)
        (q := 1 - (cell12358 ⟨37,by decide⟩).lower)
        (by norm_num [cell12358]) (by norm_num [cell12358])
      exact ⟨E.1,E.2.trans (by norm_num [cell12358])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy38 (n := 12358) (by norm_num)
        (q := 1 - (cell12358 ⟨38,by decide⟩).lower)
        (by norm_num [cell12358]) (by norm_num [cell12358])
      exact ⟨E.1,E.2.trans (by norm_num [cell12358])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy39 (n := 12358) (by norm_num)
        (q := 1 - (cell12358 ⟨39,by decide⟩).lower)
        (by norm_num [cell12358]) (by norm_num [cell12358])
      exact ⟨E.1,E.2.trans (by norm_num [cell12358])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy40 (n := 12358) (by norm_num)
        (q := 1 - (cell12358 ⟨40,by decide⟩).lower)
        (by norm_num [cell12358]) (by norm_num [cell12358])
      exact ⟨E.1,E.2.trans (by norm_num [cell12358])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy41 (n := 12358) (by norm_num)
        (q := 1 - (cell12358 ⟨41,by decide⟩).lower)
        (by norm_num [cell12358]) (by norm_num [cell12358])
      exact ⟨E.1,E.2.trans (by norm_num [cell12358])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy42 (n := 12358) (by norm_num)
        (q := 1 - (cell12358 ⟨42,by decide⟩).lower)
        (by norm_num [cell12358]) (by norm_num [cell12358])
      exact ⟨E.1,E.2.trans (by norm_num [cell12358])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy43 (n := 12358) (by norm_num)
        (q := 1 - (cell12358 ⟨43,by decide⟩).lower)
        (by norm_num [cell12358]) (by norm_num [cell12358])
      exact ⟨E.1,E.2.trans (by norm_num [cell12358])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy44 (n := 12358) (by norm_num)
        (q := 1 - (cell12358 ⟨44,by decide⟩).lower)
        (by norm_num [cell12358]) (by norm_num [cell12358])
      exact ⟨E.1,E.2.trans (by norm_num [cell12358])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy45 (n := 12358) (by norm_num)
        (q := 1 - (cell12358 ⟨45,by decide⟩).lower)
        (by norm_num [cell12358]) (by norm_num [cell12358])
      exact ⟨E.1,E.2.trans (by norm_num [cell12358])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy46 (n := 12358) (by norm_num)
        (q := 1 - (cell12358 ⟨46,by decide⟩).lower)
        (by norm_num [cell12358]) (by norm_num [cell12358])
      exact ⟨E.1,E.2.trans (by norm_num [cell12358])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy47 (n := 12358) (by norm_num)
        (q := 1 - (cell12358 ⟨47,by decide⟩).lower)
        (by norm_num [cell12358]) (by norm_num [cell12358])
      exact ⟨E.1,E.2.trans (by norm_num [cell12358])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy48 (n := 12358) (by norm_num)
        (q := 1 - (cell12358 ⟨48,by decide⟩).lower)
        (by norm_num [cell12358]) (by norm_num [cell12358])
      exact ⟨E.1,E.2.trans (by norm_num [cell12358])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy49 (n := 12358) (by norm_num)
        (q := 1 - (cell12358 ⟨49,by decide⟩).lower)
        (by norm_num [cell12358]) (by norm_num [cell12358])
      exact ⟨E.1,E.2.trans (by norm_num [cell12358])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy50 (n := 12358) (by norm_num)
        (q := 1 - (cell12358 ⟨50,by decide⟩).lower)
        (by norm_num [cell12358]) (by norm_num [cell12358])
      exact ⟨E.1,E.2.trans (by norm_num [cell12358])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy51 (n := 12358) (by norm_num)
        (q := 1 - (cell12358 ⟨51,by decide⟩).lower)
        (by norm_num [cell12358]) (by norm_num [cell12358])
      exact ⟨E.1,E.2.trans (by norm_num [cell12358])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy52 (n := 12358) (by norm_num)
        (q := 1 - (cell12358 ⟨52,by decide⟩).lower)
        (by norm_num [cell12358]) (by norm_num [cell12358])
      exact ⟨E.1,E.2.trans (by norm_num [cell12358])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12358

/-! Source-cell containment and simple scalar guards at 12358. -/
namespace BstLean.Part269.N12358
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12358)
open BstLean.Part268 (cell12358)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12358 ⟨10,by decide⟩).lower ∧ (cell12358 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12358 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12358 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12358 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12358 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12358 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12358,cell12358,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12358 ⟨11,by decide⟩).lower ∧ (cell12358 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12358 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12358 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12358 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12358 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12358 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12358,cell12358,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12358 ⟨12,by decide⟩).lower ∧ (cell12358 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12358 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12358 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12358 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12358 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12358 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12358,cell12358,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12358 ⟨13,by decide⟩).lower ∧ (cell12358 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12358 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12358 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12358 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12358 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12358 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12358,cell12358,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12358 ⟨14,by decide⟩).lower ∧ (cell12358 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12358 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12358 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12358 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12358 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12358 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12358,cell12358,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12358 ⟨15,by decide⟩).lower ∧ (cell12358 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12358 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12358 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12358 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12358 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12358 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12358,cell12358,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12358 ⟨16,by decide⟩).lower ∧ (cell12358 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12358 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12358 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12358 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12358 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12358 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12358,cell12358,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12358 ⟨17,by decide⟩).lower ∧ (cell12358 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12358 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12358 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12358 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12358 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12358 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12358,cell12358,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12358 ⟨18,by decide⟩).lower ∧ (cell12358 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12358 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12358 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12358 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12358 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12358 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12358,cell12358,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12358 ⟨19,by decide⟩).lower ∧ (cell12358 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12358 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12358 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12358 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12358 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12358 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12358,cell12358,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12358 ⟨20,by decide⟩).lower ∧ (cell12358 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12358 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12358 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12358 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12358 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12358 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12358,cell12358,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12358 ⟨21,by decide⟩).lower ∧ (cell12358 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12358 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12358 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12358 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12358 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12358 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12358,cell12358,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12358 ⟨22,by decide⟩).lower ∧ (cell12358 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12358 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12358 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12358 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12358 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12358 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12358,cell12358,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12358 ⟨23,by decide⟩).lower ∧ (cell12358 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12358 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12358 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12358 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12358 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12358 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12358,cell12358,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12358 ⟨24,by decide⟩).lower ∧ (cell12358 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12358 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12358 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12358 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12358 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12358 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12358,cell12358,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12358 ⟨25,by decide⟩).lower ∧ (cell12358 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12358 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12358 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12358 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12358 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12358 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12358,cell12358,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12358 ⟨26,by decide⟩).lower ∧ (cell12358 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12358 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12358 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12358 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12358 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12358 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12358,cell12358,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12358 ⟨27,by decide⟩).lower ∧ (cell12358 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12358 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12358 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12358 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12358 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12358 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12358,cell12358,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12358 ⟨28,by decide⟩).lower ∧ (cell12358 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12358 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12358 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12358 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12358 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12358 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12358,cell12358,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12358 ⟨29,by decide⟩).lower ∧ (cell12358 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12358 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12358 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12358 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12358 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12358 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12358,cell12358,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12358 ⟨30,by decide⟩).lower ∧ (cell12358 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12358 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12358 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12358 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12358 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12358 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12358,cell12358,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12358 ⟨31,by decide⟩).lower ∧ (cell12358 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12358 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12358 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12358 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12358 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12358 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12358,cell12358,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12358 ⟨32,by decide⟩).lower ∧ (cell12358 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12358 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12358 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12358 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12358 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12358 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12358,cell12358,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12358 ⟨33,by decide⟩).lower ∧ (cell12358 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12358 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12358 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12358 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12358 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12358 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12358,cell12358,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12358 ⟨34,by decide⟩).lower ∧ (cell12358 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12358 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12358 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12358 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12358 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12358 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12358,cell12358,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12358 ⟨35,by decide⟩).lower ∧ (cell12358 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12358 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12358 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12358 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12358 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12358 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12358,cell12358,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12358 ⟨36,by decide⟩).lower ∧ (cell12358 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12358 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12358 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12358 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12358 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12358 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12358,cell12358,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12358 ⟨37,by decide⟩).lower ∧ (cell12358 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12358 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12358 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12358 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12358 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12358 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12358,cell12358,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12358 ⟨38,by decide⟩).lower ∧ (cell12358 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12358 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12358 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12358 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12358 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12358 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12358,cell12358,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12358 ⟨39,by decide⟩).lower ∧ (cell12358 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12358 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12358 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12358 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12358 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12358 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12358,cell12358,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12358 ⟨40,by decide⟩).lower ∧ (cell12358 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12358 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12358 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12358 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12358 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12358 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12358,cell12358,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12358 ⟨41,by decide⟩).lower ∧ (cell12358 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12358 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12358 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12358 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12358 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12358 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12358,cell12358,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12358 ⟨42,by decide⟩).lower ∧ (cell12358 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12358 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12358 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12358 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12358 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12358 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12358,cell12358,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12358 ⟨43,by decide⟩).lower ∧ (cell12358 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12358 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12358 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12358 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12358 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12358 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12358,cell12358,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12358 ⟨44,by decide⟩).lower ∧ (cell12358 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12358 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12358 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12358 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12358 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12358 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12358,cell12358,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12358 ⟨45,by decide⟩).lower ∧ (cell12358 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12358 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12358 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12358 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12358 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12358 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12358,cell12358,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12358 ⟨46,by decide⟩).lower ∧ (cell12358 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12358 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12358 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12358 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12358 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12358 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12358,cell12358,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12358 ⟨47,by decide⟩).lower ∧ (cell12358 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12358 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12358 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12358 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12358 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12358 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12358,cell12358,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12358 ⟨48,by decide⟩).lower ∧ (cell12358 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12358 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12358 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12358 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12358 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12358 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12358,cell12358,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12358 ⟨49,by decide⟩).lower ∧ (cell12358 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12358 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12358 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12358 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12358 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12358 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12358,cell12358,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12358 ⟨50,by decide⟩).lower ∧ (cell12358 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12358 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12358 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12358 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12358 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12358 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12358,cell12358,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12358 ⟨51,by decide⟩).lower ∧ (cell12358 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12358 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12358 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12358 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12358 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12358 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12358,cell12358,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12358 ⟨52,by decide⟩).lower ∧ (cell12358 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12358 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12358 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12358 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12358 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12358 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12358,cell12358,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12358 i).lower ∧
    (cell12358 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12358 i).upper ≤ (0.532 : ℝ) ∧
    (cell12358 i).centre ≤ (0.1 : ℝ) ∧ (cell12358 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12358 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12358 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12358

/-! The local source numeric instances at 12358 have no network premises. -/
namespace BstLean.Part269.N12358
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12358)
open BstLean.Part268 (cell12358)

noncomputable def sourceNumerics12358 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12358 (cell12358 i)
      scalarRow12358.M scalarRow12358.H scalarRow12358.xi := by
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
    energy_allowance := scalarRow12358.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12358]
    centre_nonneg := (scalarRow12358.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D0.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12358])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12358
/-! Actual 12359 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12359
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12359 ≤ (1.036304244484 : ℝ) := by
  have hr : (111.171039394259 : ℝ) ≤ √(12359 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.171039394259 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12359 12359 (11 / 1000) ≤
    (0.008598346617 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12359) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.171039394259 : ℝ) ≤ √(12359 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12359)
  have hdiv : K / √(12359 : ℝ) ≤ K / 111.171039394259 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.171039394259 ≤ (0.008598346617 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12359.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12359 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12359 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12359 := gPlus_lower 12359
end BstLean.Part269.N12359

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12359
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036304244483 : ℝ) ≤ wn 12359 := by
  have hn : √(12359 : ℝ) ≤ 111.171039394260 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12359 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.171039394260 ≤ 2 / √(12359 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000258954269 : ℝ) ≤ rhoBar 12359 BstLean.Part154.csC ∧
    rhoBar 12359 BstLean.Part154.csC ≤ 0.000258954670 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036304244483 : ℝ) / (1.295212 * 12359) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036304244484 : ℝ) / (1.29521 * 12359) := by gcongr
      _ ≤ (0.000258954670 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12359 BstLean.Part154.csC) ≤ 0.001035885738 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12359 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12359 BstLean.Part154.csC) (piBar (rhoBar 12359 BstLean.Part154.csC)) ≤ 0.000197791582 ∧
    cc1 (rhoBar 12359 BstLean.Part154.csC) (piBar (rhoBar 12359 BstLean.Part154.csC)) ≤ 0.000125856044 ∧
    cc2 (rhoBar 12359 BstLean.Part154.csC) ≤ 0.000073060333 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12359 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12359 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12359 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12359 BstLean.Part154.csC * nuR (rhoBar 12359 BstLean.Part154.csC)) ≤ 0.000517926105 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000258954670 : ℝ) * 0.001035885738 := by gcongr
      _ ≤ (0.000517926105 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12359 BstLean.Part154.csC) * nuR (rhoBar 12359 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001035885738 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12359 BstLean.Part154.csC) * rhoBar 12359 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000258954670 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000258954670 / 2 + 0.399 * 0.001035885738 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000197791582 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000517926105 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125856044 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000258954670 / 1.414213562 := by gcongr
      _ ≤ (0.000073060333 : ℝ) := by norm_num

end BstLean.Part269.N12359

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12359
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12359 BstLean.Part154.csC) (piBar (rhoBar 12359 BstLean.Part154.csC)) ≤ 1.68947E-7 := by
  have hr0 : 0 ≤ rhoBar 12359 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12359 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12359 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12359 BstLean.Part154.csC) (piBar (rhoBar 12359 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12359 BstLean.Part154.csC) (piBar (rhoBar 12359 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12359 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000197791582 : ℝ) ^ 2 + 0.000125856044 ^ 2 + 3 * 0.000073060333 ^ 2 +
        2 * 0.797885 * 0.000197791582 * 0.000125856044 + 2 * 0.000197791582 * 0.000073060333 +
        4 * 0.797885 * 0.000125856044 * 0.000073060333 := by gcongr
    _ ≤ (1.68947E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12359 BstLean.Part154.csC Θ ≤ 0.002704423355 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12359 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12359 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12359 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12359 BstLean.Part154.csC) (piBar (rhoBar 12359 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12359 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036304244484 * 1.68947E-7 / (0.000258954269 : ℝ) := by gcongr
    _ ≤ 0.002704423355 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12359 BstLean.Part154.csC Θ ≤ 0.003002136387 + 0.000683362636 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12359 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12359 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12359 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036304244484 : ℝ) * ((2 * Θ * 0.000258954670 +
        (6863 / 10000) * 0.000258954670 * 12359 * 0.001035885738) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003002136387 + 0.000683362636 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12359 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12359 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12359 0.011 Θ ∧ gammaRatio 12359 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12359 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036304244484 : ℝ) * 0.525 / ((1 - 0.011) * 12359) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12359 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12359 0.011 Θ) :=
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
    badAllowance 12359 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12359 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12359 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12359 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12359 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12359 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12359 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12359 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12359 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12359 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12359 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036304244484 : ℝ) * 12359 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12359 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004102136387 + 0.003387785991 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12359

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12359
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12359 BstLean.Part154.csC) (piBar (rhoBar 12359 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12359 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12359 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12359 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12359 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12359 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12359 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12359 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12359 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12359 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12359 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12359 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12359 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12359 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12359 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053211344170 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12359) ≤ 0.010742344298 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12359 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036304244484)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010742344298 + 2 * 0.737676 / 12359) := by gcongr
    _ ≤ (0.053211344170 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12359 12 ≤ 0.0015 := by
  exact BstLean.Part269.S0.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12359

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12359
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560487721773 : ℝ) ≤ plow 12359 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12359) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053387324033)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001419822262) : eMP 12359 0.011 xi bn ≤ 0.001221903089 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12359 : ℝ) * (1 - 0.011))) ≤ 0.000604090686 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001419822262 / (12359 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000604090686 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000604090686 : ℝ) + 3.141593 * 0.053387324033 / (12359 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001221903089 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053387324033)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001419822262) : PiBarMP 12359 12 0.011 xi bn ≤ 0.163484946930 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12359 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037680528951 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.557907903505 : ℝ) ≤ √((12359 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.171039394259 : ℝ) ≤ √(12359 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12359) ≤ 0.125324080253 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037680528951 + 0.053387324033 * 1.772454 / (2 * (110.557907903505 : ℝ))) * (1 + 0.001221903089) +
        8 / (12359 * 111.171039394259) + 0.125324080253 := by gcongr
    _ ≤ (0.163484946930 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053387324033)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001419822262) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284268315571) :
    parallelOracle 12359 0.011 xi bn cd ≤ 0.164506308353 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12359 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12359 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560487721773 : ℝ) ≤ plow 12359 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.171039394259 : ℝ) ≤ √(12359 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284268315571 : ℝ) / (2 * 0.560487721773 * 111.171039394259)) * 0.163484946930 +
        0.284268315571 ^ 2 / (2 * 0.560487721773 * 111.171039394259) := by gcongr
    _ ≤ (0.164506308353 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053387324033) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001419822262)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284268315571) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12359 12359 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560487721773 : ℝ) ≤ plow 12359 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.171039394259 : ℝ) ≤ √(12359 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12359 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12359 Θ 1.22 ≤ 0.011928470826 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.171039394259 := by gcongr <;> linarith
      _ ≤ (0.011928470826 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12359 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12359 12359 0.011 ≤ 0.008598346617 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12359 12359 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12359 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12359 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12359 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12359 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164506308353 + 0.011928470826 + (0.008598346617 : ℝ) *
        (1 + 2 * (0.284268315571 + 0.011928470826) / (0.560487721773 * 111.171039394259))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12359]

end BstLean.Part269.N12359

/-! The original eight local profiles supply actual 12359 moment certificates. -/
namespace BstLean.Part269.N12359
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12359 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12359 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12359 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053387324033 ∧
    0 ≤ bN 12359 BstLean.Part154.csC (groupTheta g) ∧ bN 12359 BstLean.Part154.csC (groupTheta g) ≤ 0.001419822262 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12359 12359 0.011
      (momentAllowance 12359 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12359 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12359 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12359 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12359 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12359 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231056971401 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12359 0.011
      (momentAllowance 12359 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12359 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12359
/-! The actual computed-centre upper energy formula at 12359. -/
namespace BstLean.Part269.N12359
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12359

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12359
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12359)
open BstLean.Part268 (cell12359)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086555866191
  | 2 => 0.087519902326
  | 3 => 0.088485450222
  | 4 => 0.089454683275
  | 5 => 0.090430201643
  | 6 => 0.091415091789
  | 7 => 0.092412990930
  | 8 => 0.093428156337
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12359 12359 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12359 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004104440387 + 0.003390347157 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S0.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12359

/-! Actual upper energy certificates on all 43 source endpoints at 12359. -/
namespace BstLean.Part269.N12359
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12359)
open BstLean.Part268 (cell12359)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12359 (gMinus 12359) (1 - (cell12359 i).lower) ≤ 1 ∧
    energyUpper 12359 (gMinus 12359) (BstLean.Part211.gPlus 12359)
      (finiteEnergy 12359 12359 0.011) (1 - (cell12359 i).lower) ≤
      (cell12359 i).energy := by
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
      have E := BstLean.Part269.S0.uniformEnergy10 (n := 12359) (by norm_num)
        (q := 1 - (cell12359 ⟨10,by decide⟩).lower)
        (by norm_num [cell12359]) (by norm_num [cell12359])
      exact ⟨E.1,E.2.trans (by norm_num [cell12359])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy11 (n := 12359) (by norm_num)
        (q := 1 - (cell12359 ⟨11,by decide⟩).lower)
        (by norm_num [cell12359]) (by norm_num [cell12359])
      exact ⟨E.1,E.2.trans (by norm_num [cell12359])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy12 (n := 12359) (by norm_num)
        (q := 1 - (cell12359 ⟨12,by decide⟩).lower)
        (by norm_num [cell12359]) (by norm_num [cell12359])
      exact ⟨E.1,E.2.trans (by norm_num [cell12359])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy13 (n := 12359) (by norm_num)
        (q := 1 - (cell12359 ⟨13,by decide⟩).lower)
        (by norm_num [cell12359]) (by norm_num [cell12359])
      exact ⟨E.1,E.2.trans (by norm_num [cell12359])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy14 (n := 12359) (by norm_num)
        (q := 1 - (cell12359 ⟨14,by decide⟩).lower)
        (by norm_num [cell12359]) (by norm_num [cell12359])
      exact ⟨E.1,E.2.trans (by norm_num [cell12359])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy15 (n := 12359) (by norm_num)
        (q := 1 - (cell12359 ⟨15,by decide⟩).lower)
        (by norm_num [cell12359]) (by norm_num [cell12359])
      exact ⟨E.1,E.2.trans (by norm_num [cell12359])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy16 (n := 12359) (by norm_num)
        (q := 1 - (cell12359 ⟨16,by decide⟩).lower)
        (by norm_num [cell12359]) (by norm_num [cell12359])
      exact ⟨E.1,E.2.trans (by norm_num [cell12359])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy17 (n := 12359) (by norm_num)
        (q := 1 - (cell12359 ⟨17,by decide⟩).lower)
        (by norm_num [cell12359]) (by norm_num [cell12359])
      exact ⟨E.1,E.2.trans (by norm_num [cell12359])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy18 (n := 12359) (by norm_num)
        (q := 1 - (cell12359 ⟨18,by decide⟩).lower)
        (by norm_num [cell12359]) (by norm_num [cell12359])
      exact ⟨E.1,E.2.trans (by norm_num [cell12359])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy19 (n := 12359) (by norm_num)
        (q := 1 - (cell12359 ⟨19,by decide⟩).lower)
        (by norm_num [cell12359]) (by norm_num [cell12359])
      exact ⟨E.1,E.2.trans (by norm_num [cell12359])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy20 (n := 12359) (by norm_num)
        (q := 1 - (cell12359 ⟨20,by decide⟩).lower)
        (by norm_num [cell12359]) (by norm_num [cell12359])
      exact ⟨E.1,E.2.trans (by norm_num [cell12359])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy21 (n := 12359) (by norm_num)
        (q := 1 - (cell12359 ⟨21,by decide⟩).lower)
        (by norm_num [cell12359]) (by norm_num [cell12359])
      exact ⟨E.1,E.2.trans (by norm_num [cell12359])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy22 (n := 12359) (by norm_num)
        (q := 1 - (cell12359 ⟨22,by decide⟩).lower)
        (by norm_num [cell12359]) (by norm_num [cell12359])
      exact ⟨E.1,E.2.trans (by norm_num [cell12359])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy23 (n := 12359) (by norm_num)
        (q := 1 - (cell12359 ⟨23,by decide⟩).lower)
        (by norm_num [cell12359]) (by norm_num [cell12359])
      exact ⟨E.1,E.2.trans (by norm_num [cell12359])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy24 (n := 12359) (by norm_num)
        (q := 1 - (cell12359 ⟨24,by decide⟩).lower)
        (by norm_num [cell12359]) (by norm_num [cell12359])
      exact ⟨E.1,E.2.trans (by norm_num [cell12359])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy25 (n := 12359) (by norm_num)
        (q := 1 - (cell12359 ⟨25,by decide⟩).lower)
        (by norm_num [cell12359]) (by norm_num [cell12359])
      exact ⟨E.1,E.2.trans (by norm_num [cell12359])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy26 (n := 12359) (by norm_num)
        (q := 1 - (cell12359 ⟨26,by decide⟩).lower)
        (by norm_num [cell12359]) (by norm_num [cell12359])
      exact ⟨E.1,E.2.trans (by norm_num [cell12359])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy27 (n := 12359) (by norm_num)
        (q := 1 - (cell12359 ⟨27,by decide⟩).lower)
        (by norm_num [cell12359]) (by norm_num [cell12359])
      exact ⟨E.1,E.2.trans (by norm_num [cell12359])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy28 (n := 12359) (by norm_num)
        (q := 1 - (cell12359 ⟨28,by decide⟩).lower)
        (by norm_num [cell12359]) (by norm_num [cell12359])
      exact ⟨E.1,E.2.trans (by norm_num [cell12359])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy29 (n := 12359) (by norm_num)
        (q := 1 - (cell12359 ⟨29,by decide⟩).lower)
        (by norm_num [cell12359]) (by norm_num [cell12359])
      exact ⟨E.1,E.2.trans (by norm_num [cell12359])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy30 (n := 12359) (by norm_num)
        (q := 1 - (cell12359 ⟨30,by decide⟩).lower)
        (by norm_num [cell12359]) (by norm_num [cell12359])
      exact ⟨E.1,E.2.trans (by norm_num [cell12359])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy31 (n := 12359) (by norm_num)
        (q := 1 - (cell12359 ⟨31,by decide⟩).lower)
        (by norm_num [cell12359]) (by norm_num [cell12359])
      exact ⟨E.1,E.2.trans (by norm_num [cell12359])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy32 (n := 12359) (by norm_num)
        (q := 1 - (cell12359 ⟨32,by decide⟩).lower)
        (by norm_num [cell12359]) (by norm_num [cell12359])
      exact ⟨E.1,E.2.trans (by norm_num [cell12359])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy33 (n := 12359) (by norm_num)
        (q := 1 - (cell12359 ⟨33,by decide⟩).lower)
        (by norm_num [cell12359]) (by norm_num [cell12359])
      exact ⟨E.1,E.2.trans (by norm_num [cell12359])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy34 (n := 12359) (by norm_num)
        (q := 1 - (cell12359 ⟨34,by decide⟩).lower)
        (by norm_num [cell12359]) (by norm_num [cell12359])
      exact ⟨E.1,E.2.trans (by norm_num [cell12359])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy35 (n := 12359) (by norm_num)
        (q := 1 - (cell12359 ⟨35,by decide⟩).lower)
        (by norm_num [cell12359]) (by norm_num [cell12359])
      exact ⟨E.1,E.2.trans (by norm_num [cell12359])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy36 (n := 12359) (by norm_num)
        (q := 1 - (cell12359 ⟨36,by decide⟩).lower)
        (by norm_num [cell12359]) (by norm_num [cell12359])
      exact ⟨E.1,E.2.trans (by norm_num [cell12359])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy37 (n := 12359) (by norm_num)
        (q := 1 - (cell12359 ⟨37,by decide⟩).lower)
        (by norm_num [cell12359]) (by norm_num [cell12359])
      exact ⟨E.1,E.2.trans (by norm_num [cell12359])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy38 (n := 12359) (by norm_num)
        (q := 1 - (cell12359 ⟨38,by decide⟩).lower)
        (by norm_num [cell12359]) (by norm_num [cell12359])
      exact ⟨E.1,E.2.trans (by norm_num [cell12359])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy39 (n := 12359) (by norm_num)
        (q := 1 - (cell12359 ⟨39,by decide⟩).lower)
        (by norm_num [cell12359]) (by norm_num [cell12359])
      exact ⟨E.1,E.2.trans (by norm_num [cell12359])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy40 (n := 12359) (by norm_num)
        (q := 1 - (cell12359 ⟨40,by decide⟩).lower)
        (by norm_num [cell12359]) (by norm_num [cell12359])
      exact ⟨E.1,E.2.trans (by norm_num [cell12359])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy41 (n := 12359) (by norm_num)
        (q := 1 - (cell12359 ⟨41,by decide⟩).lower)
        (by norm_num [cell12359]) (by norm_num [cell12359])
      exact ⟨E.1,E.2.trans (by norm_num [cell12359])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy42 (n := 12359) (by norm_num)
        (q := 1 - (cell12359 ⟨42,by decide⟩).lower)
        (by norm_num [cell12359]) (by norm_num [cell12359])
      exact ⟨E.1,E.2.trans (by norm_num [cell12359])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy43 (n := 12359) (by norm_num)
        (q := 1 - (cell12359 ⟨43,by decide⟩).lower)
        (by norm_num [cell12359]) (by norm_num [cell12359])
      exact ⟨E.1,E.2.trans (by norm_num [cell12359])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy44 (n := 12359) (by norm_num)
        (q := 1 - (cell12359 ⟨44,by decide⟩).lower)
        (by norm_num [cell12359]) (by norm_num [cell12359])
      exact ⟨E.1,E.2.trans (by norm_num [cell12359])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy45 (n := 12359) (by norm_num)
        (q := 1 - (cell12359 ⟨45,by decide⟩).lower)
        (by norm_num [cell12359]) (by norm_num [cell12359])
      exact ⟨E.1,E.2.trans (by norm_num [cell12359])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy46 (n := 12359) (by norm_num)
        (q := 1 - (cell12359 ⟨46,by decide⟩).lower)
        (by norm_num [cell12359]) (by norm_num [cell12359])
      exact ⟨E.1,E.2.trans (by norm_num [cell12359])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy47 (n := 12359) (by norm_num)
        (q := 1 - (cell12359 ⟨47,by decide⟩).lower)
        (by norm_num [cell12359]) (by norm_num [cell12359])
      exact ⟨E.1,E.2.trans (by norm_num [cell12359])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy48 (n := 12359) (by norm_num)
        (q := 1 - (cell12359 ⟨48,by decide⟩).lower)
        (by norm_num [cell12359]) (by norm_num [cell12359])
      exact ⟨E.1,E.2.trans (by norm_num [cell12359])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy49 (n := 12359) (by norm_num)
        (q := 1 - (cell12359 ⟨49,by decide⟩).lower)
        (by norm_num [cell12359]) (by norm_num [cell12359])
      exact ⟨E.1,E.2.trans (by norm_num [cell12359])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy50 (n := 12359) (by norm_num)
        (q := 1 - (cell12359 ⟨50,by decide⟩).lower)
        (by norm_num [cell12359]) (by norm_num [cell12359])
      exact ⟨E.1,E.2.trans (by norm_num [cell12359])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy51 (n := 12359) (by norm_num)
        (q := 1 - (cell12359 ⟨51,by decide⟩).lower)
        (by norm_num [cell12359]) (by norm_num [cell12359])
      exact ⟨E.1,E.2.trans (by norm_num [cell12359])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy52 (n := 12359) (by norm_num)
        (q := 1 - (cell12359 ⟨52,by decide⟩).lower)
        (by norm_num [cell12359]) (by norm_num [cell12359])
      exact ⟨E.1,E.2.trans (by norm_num [cell12359])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12359

/-! Source-cell containment and simple scalar guards at 12359. -/
namespace BstLean.Part269.N12359
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12359)
open BstLean.Part268 (cell12359)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12359 ⟨10,by decide⟩).lower ∧ (cell12359 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12359 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12359 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12359 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12359 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12359 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12359,cell12359,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12359 ⟨11,by decide⟩).lower ∧ (cell12359 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12359 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12359 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12359 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12359 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12359 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12359,cell12359,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12359 ⟨12,by decide⟩).lower ∧ (cell12359 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12359 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12359 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12359 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12359 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12359 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12359,cell12359,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12359 ⟨13,by decide⟩).lower ∧ (cell12359 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12359 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12359 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12359 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12359 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12359 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12359,cell12359,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12359 ⟨14,by decide⟩).lower ∧ (cell12359 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12359 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12359 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12359 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12359 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12359 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12359,cell12359,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12359 ⟨15,by decide⟩).lower ∧ (cell12359 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12359 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12359 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12359 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12359 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12359 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12359,cell12359,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12359 ⟨16,by decide⟩).lower ∧ (cell12359 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12359 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12359 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12359 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12359 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12359 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12359,cell12359,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12359 ⟨17,by decide⟩).lower ∧ (cell12359 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12359 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12359 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12359 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12359 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12359 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12359,cell12359,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12359 ⟨18,by decide⟩).lower ∧ (cell12359 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12359 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12359 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12359 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12359 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12359 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12359,cell12359,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12359 ⟨19,by decide⟩).lower ∧ (cell12359 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12359 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12359 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12359 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12359 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12359 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12359,cell12359,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12359 ⟨20,by decide⟩).lower ∧ (cell12359 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12359 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12359 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12359 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12359 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12359 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12359,cell12359,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12359 ⟨21,by decide⟩).lower ∧ (cell12359 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12359 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12359 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12359 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12359 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12359 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12359,cell12359,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12359 ⟨22,by decide⟩).lower ∧ (cell12359 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12359 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12359 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12359 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12359 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12359 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12359,cell12359,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12359 ⟨23,by decide⟩).lower ∧ (cell12359 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12359 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12359 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12359 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12359 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12359 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12359,cell12359,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12359 ⟨24,by decide⟩).lower ∧ (cell12359 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12359 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12359 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12359 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12359 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12359 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12359,cell12359,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12359 ⟨25,by decide⟩).lower ∧ (cell12359 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12359 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12359 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12359 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12359 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12359 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12359,cell12359,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12359 ⟨26,by decide⟩).lower ∧ (cell12359 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12359 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12359 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12359 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12359 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12359 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12359,cell12359,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12359 ⟨27,by decide⟩).lower ∧ (cell12359 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12359 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12359 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12359 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12359 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12359 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12359,cell12359,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12359 ⟨28,by decide⟩).lower ∧ (cell12359 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12359 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12359 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12359 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12359 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12359 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12359,cell12359,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12359 ⟨29,by decide⟩).lower ∧ (cell12359 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12359 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12359 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12359 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12359 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12359 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12359,cell12359,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12359 ⟨30,by decide⟩).lower ∧ (cell12359 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12359 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12359 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12359 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12359 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12359 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12359,cell12359,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12359 ⟨31,by decide⟩).lower ∧ (cell12359 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12359 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12359 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12359 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12359 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12359 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12359,cell12359,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12359 ⟨32,by decide⟩).lower ∧ (cell12359 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12359 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12359 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12359 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12359 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12359 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12359,cell12359,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12359 ⟨33,by decide⟩).lower ∧ (cell12359 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12359 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12359 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12359 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12359 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12359 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12359,cell12359,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12359 ⟨34,by decide⟩).lower ∧ (cell12359 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12359 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12359 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12359 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12359 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12359 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12359,cell12359,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12359 ⟨35,by decide⟩).lower ∧ (cell12359 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12359 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12359 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12359 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12359 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12359 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12359,cell12359,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12359 ⟨36,by decide⟩).lower ∧ (cell12359 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12359 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12359 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12359 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12359 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12359 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12359,cell12359,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12359 ⟨37,by decide⟩).lower ∧ (cell12359 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12359 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12359 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12359 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12359 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12359 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12359,cell12359,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12359 ⟨38,by decide⟩).lower ∧ (cell12359 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12359 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12359 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12359 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12359 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12359 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12359,cell12359,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12359 ⟨39,by decide⟩).lower ∧ (cell12359 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12359 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12359 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12359 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12359 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12359 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12359,cell12359,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12359 ⟨40,by decide⟩).lower ∧ (cell12359 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12359 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12359 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12359 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12359 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12359 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12359,cell12359,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12359 ⟨41,by decide⟩).lower ∧ (cell12359 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12359 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12359 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12359 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12359 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12359 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12359,cell12359,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12359 ⟨42,by decide⟩).lower ∧ (cell12359 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12359 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12359 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12359 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12359 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12359 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12359,cell12359,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12359 ⟨43,by decide⟩).lower ∧ (cell12359 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12359 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12359 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12359 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12359 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12359 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12359,cell12359,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12359 ⟨44,by decide⟩).lower ∧ (cell12359 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12359 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12359 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12359 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12359 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12359 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12359,cell12359,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12359 ⟨45,by decide⟩).lower ∧ (cell12359 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12359 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12359 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12359 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12359 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12359 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12359,cell12359,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12359 ⟨46,by decide⟩).lower ∧ (cell12359 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12359 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12359 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12359 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12359 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12359 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12359,cell12359,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12359 ⟨47,by decide⟩).lower ∧ (cell12359 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12359 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12359 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12359 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12359 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12359 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12359,cell12359,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12359 ⟨48,by decide⟩).lower ∧ (cell12359 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12359 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12359 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12359 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12359 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12359 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12359,cell12359,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12359 ⟨49,by decide⟩).lower ∧ (cell12359 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12359 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12359 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12359 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12359 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12359 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12359,cell12359,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12359 ⟨50,by decide⟩).lower ∧ (cell12359 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12359 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12359 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12359 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12359 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12359 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12359,cell12359,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12359 ⟨51,by decide⟩).lower ∧ (cell12359 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12359 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12359 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12359 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12359 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12359 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12359,cell12359,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12359 ⟨52,by decide⟩).lower ∧ (cell12359 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12359 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12359 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12359 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12359 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12359 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12359,cell12359,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12359 i).lower ∧
    (cell12359 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12359 i).upper ≤ (0.532 : ℝ) ∧
    (cell12359 i).centre ≤ (0.1 : ℝ) ∧ (cell12359 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12359 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12359 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12359

/-! The local source numeric instances at 12359 have no network premises. -/
namespace BstLean.Part269.N12359
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12359)
open BstLean.Part268 (cell12359)

noncomputable def sourceNumerics12359 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12359 (cell12359 i)
      scalarRow12359.M scalarRow12359.H scalarRow12359.xi := by
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
    energy_allowance := scalarRow12359.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12359]
    centre_nonneg := (scalarRow12359.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D0.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12359])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12359
/-! Actual 12360 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12360
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12360 ≤ (1.036302762744 : ℝ) := by
  have hr : (111.175536877498 : ℝ) ≤ √(12360 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.175536877498 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12360 12360 (11 / 1000) ≤
    (0.008597998778 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12360) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.175536877498 : ℝ) ≤ √(12360 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12360)
  have hdiv : K / √(12360 : ℝ) ≤ K / 111.175536877498 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.175536877498 ≤ (0.008597998778 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12360.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12360 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12360 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12360 := gPlus_lower 12360
end BstLean.Part269.N12360

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12360
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036302762743 : ℝ) ≤ wn 12360 := by
  have hn : √(12360 : ℝ) ≤ 111.175536877499 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12360 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.175536877499 ≤ 2 / √(12360 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000258932948 : ℝ) ≤ rhoBar 12360 BstLean.Part154.csC ∧
    rhoBar 12360 BstLean.Part154.csC ≤ 0.000258933349 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036302762743 : ℝ) / (1.295212 * 12360) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036302762744 : ℝ) / (1.29521 * 12360) := by gcongr
      _ ≤ (0.000258933349 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12360 BstLean.Part154.csC) ≤ 0.001035800443 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12360 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12360 BstLean.Part154.csC) (piBar (rhoBar 12360 BstLean.Part154.csC)) ≤ 0.000197775296 ∧
    cc1 (rhoBar 12360 BstLean.Part154.csC) (piBar (rhoBar 12360 BstLean.Part154.csC)) ≤ 0.000125845681 ∧
    cc2 (rhoBar 12360 BstLean.Part154.csC) ≤ 0.000073054318 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12360 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12360 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12360 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12360 BstLean.Part154.csC * nuR (rhoBar 12360 BstLean.Part154.csC)) ≤ 0.000517883460 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000258933349 : ℝ) * 0.001035800443 := by gcongr
      _ ≤ (0.000517883460 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12360 BstLean.Part154.csC) * nuR (rhoBar 12360 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001035800443 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12360 BstLean.Part154.csC) * rhoBar 12360 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000258933349 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000258933349 / 2 + 0.399 * 0.001035800443 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000197775296 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000517883460 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125845681 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000258933349 / 1.414213562 := by gcongr
      _ ≤ (0.000073054318 : ℝ) := by norm_num

end BstLean.Part269.N12360

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12360
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12360 BstLean.Part154.csC) (piBar (rhoBar 12360 BstLean.Part154.csC)) ≤ 1.68919E-7 := by
  have hr0 : 0 ≤ rhoBar 12360 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12360 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12360 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12360 BstLean.Part154.csC) (piBar (rhoBar 12360 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12360 BstLean.Part154.csC) (piBar (rhoBar 12360 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12360 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000197775296 : ℝ) ^ 2 + 0.000125845681 ^ 2 + 3 * 0.000073054318 ^ 2 +
        2 * 0.797885 * 0.000197775296 * 0.000125845681 + 2 * 0.000197775296 * 0.000073054318 +
        4 * 0.797885 * 0.000125845681 * 0.000073054318 := by gcongr
    _ ≤ (1.68919E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12360 BstLean.Part154.csC Θ ≤ 0.002704193928 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12360 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12360 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12360 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12360 BstLean.Part154.csC) (piBar (rhoBar 12360 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12360 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036302762744 * 1.68919E-7 / (0.000258932948 : ℝ) := by gcongr
    _ ≤ 0.002704193928 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12360 BstLean.Part154.csC Θ ≤ 0.003001880610 + 0.000683305395 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12360 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12360 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12360 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036302762744 : ℝ) * ((2 * Θ * 0.000258933349 +
        (6863 / 10000) * 0.000258933349 * 12360 * 0.001035800443) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003001880610 + 0.000683305395 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12360 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12360 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12360 0.011 Θ ∧ gammaRatio 12360 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12360 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036302762744 : ℝ) * 0.525 / ((1 - 0.011) * 12360) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12360 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12360 0.011 Θ) :=
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
    badAllowance 12360 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12360 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12360 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12360 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12360 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12360 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12360 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12360 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12360 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12360 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12360 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036302762744 : ℝ) * 12360 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12360 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004101880610 + 0.003387499323 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12360

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12360
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12360 BstLean.Part154.csC) (piBar (rhoBar 12360 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12360 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12360 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12360 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12360 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12360 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12360 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12360 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12360 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12360 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12360 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12360 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12360 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12360 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12360 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053209167905 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12360) ≤ 0.010741909728 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12360 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036302762744)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010741909728 + 2 * 0.737676 / 12360) := by gcongr
    _ ≤ (0.053209167905 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12360 12 ≤ 0.0015 := by
  exact BstLean.Part269.S0.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12360

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12360
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560487769522 : ℝ) ≤ plow 12360 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12360) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053386917755)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001419701813) : eMP 12360 0.011 xi bn ≤ 0.001221801753 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12360 : ℝ) * (1 - 0.011))) ≤ 0.000604040625 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001419701813 / (12360 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000604040625 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000604040625 : ℝ) + 3.141593 * 0.053386917755 / (12360 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001221801753 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053386917755)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001419701813) : PiBarMP 12360 12 0.011 xi bn ≤ 0.163478251642 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12360 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037678930625 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.562380582185 : ℝ) ≤ √((12360 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.175536877498 : ℝ) ≤ √(12360 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12360) ≤ 0.125319010406 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037678930625 + 0.053386917755 * 1.772454 / (2 * (110.562380582185 : ℝ))) * (1 + 0.001221801753) +
        8 / (12360 * 111.175536877498) + 0.125319010406 := by gcongr
    _ ≤ (0.163478251642 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053386917755)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001419701813) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284265260132) :
    parallelOracle 12360 0.011 xi bn cd ≤ 0.164499538441 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12360 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12360 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560487769522 : ℝ) ≤ plow 12360 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.175536877498 : ℝ) ≤ √(12360 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284265260132 : ℝ) / (2 * 0.560487769522 * 111.175536877498)) * 0.163478251642 +
        0.284265260132 ^ 2 / (2 * 0.560487769522 * 111.175536877498) := by gcongr
    _ ≤ (0.164499538441 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053386917755) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001419701813)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284265260132) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12360 12360 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560487769522 : ℝ) ≤ plow 12360 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.175536877498 : ℝ) ≤ √(12360 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12360 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12360 Θ 1.22 ≤ 0.011927988272 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.175536877498 := by gcongr <;> linarith
      _ ≤ (0.011927988272 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12360 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12360 12360 0.011 ≤ 0.008597998778 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12360 12360 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12360 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12360 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12360 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12360 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164499538441 + 0.011927988272 + (0.008597998778 : ℝ) *
        (1 + 2 * (0.284265260132 + 0.011927988272) / (0.560487769522 * 111.175536877498))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12360]

end BstLean.Part269.N12360

/-! The original eight local profiles supply actual 12360 moment certificates. -/
namespace BstLean.Part269.N12360
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12360 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12360 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12360 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053386917755 ∧
    0 ≤ bN 12360 BstLean.Part154.csC (groupTheta g) ∧ bN 12360 BstLean.Part154.csC (groupTheta g) ≤ 0.001419701813 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12360 12360 0.011
      (momentAllowance 12360 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12360 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12360 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12360 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12360 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12360 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231056092227 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12360 0.011
      (momentAllowance 12360 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12360 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12360
/-! The actual computed-centre upper energy formula at 12360. -/
namespace BstLean.Part269.N12360
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12360

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12360
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12360)
open BstLean.Part268 (cell12360)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086552506681
  | 2 => 0.087516470163
  | 3 => 0.088481933129
  | 4 => 0.089451066290
  | 5 => 0.090426466673
  | 6 => 0.091411217102
  | 7 => 0.092408950609
  | 8 => 0.093423919669
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12360 12360 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12360 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004104440387 + 0.003390347157 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S0.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12360

/-! Actual upper energy certificates on all 43 source endpoints at 12360. -/
namespace BstLean.Part269.N12360
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12360)
open BstLean.Part268 (cell12360)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12360 (gMinus 12360) (1 - (cell12360 i).lower) ≤ 1 ∧
    energyUpper 12360 (gMinus 12360) (BstLean.Part211.gPlus 12360)
      (finiteEnergy 12360 12360 0.011) (1 - (cell12360 i).lower) ≤
      (cell12360 i).energy := by
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
      have E := BstLean.Part269.S0.uniformEnergy10 (n := 12360) (by norm_num)
        (q := 1 - (cell12360 ⟨10,by decide⟩).lower)
        (by norm_num [cell12360]) (by norm_num [cell12360])
      exact ⟨E.1,E.2.trans (by norm_num [cell12360])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy11 (n := 12360) (by norm_num)
        (q := 1 - (cell12360 ⟨11,by decide⟩).lower)
        (by norm_num [cell12360]) (by norm_num [cell12360])
      exact ⟨E.1,E.2.trans (by norm_num [cell12360])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy12 (n := 12360) (by norm_num)
        (q := 1 - (cell12360 ⟨12,by decide⟩).lower)
        (by norm_num [cell12360]) (by norm_num [cell12360])
      exact ⟨E.1,E.2.trans (by norm_num [cell12360])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy13 (n := 12360) (by norm_num)
        (q := 1 - (cell12360 ⟨13,by decide⟩).lower)
        (by norm_num [cell12360]) (by norm_num [cell12360])
      exact ⟨E.1,E.2.trans (by norm_num [cell12360])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy14 (n := 12360) (by norm_num)
        (q := 1 - (cell12360 ⟨14,by decide⟩).lower)
        (by norm_num [cell12360]) (by norm_num [cell12360])
      exact ⟨E.1,E.2.trans (by norm_num [cell12360])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy15 (n := 12360) (by norm_num)
        (q := 1 - (cell12360 ⟨15,by decide⟩).lower)
        (by norm_num [cell12360]) (by norm_num [cell12360])
      exact ⟨E.1,E.2.trans (by norm_num [cell12360])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy16 (n := 12360) (by norm_num)
        (q := 1 - (cell12360 ⟨16,by decide⟩).lower)
        (by norm_num [cell12360]) (by norm_num [cell12360])
      exact ⟨E.1,E.2.trans (by norm_num [cell12360])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy17 (n := 12360) (by norm_num)
        (q := 1 - (cell12360 ⟨17,by decide⟩).lower)
        (by norm_num [cell12360]) (by norm_num [cell12360])
      exact ⟨E.1,E.2.trans (by norm_num [cell12360])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy18 (n := 12360) (by norm_num)
        (q := 1 - (cell12360 ⟨18,by decide⟩).lower)
        (by norm_num [cell12360]) (by norm_num [cell12360])
      exact ⟨E.1,E.2.trans (by norm_num [cell12360])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy19 (n := 12360) (by norm_num)
        (q := 1 - (cell12360 ⟨19,by decide⟩).lower)
        (by norm_num [cell12360]) (by norm_num [cell12360])
      exact ⟨E.1,E.2.trans (by norm_num [cell12360])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy20 (n := 12360) (by norm_num)
        (q := 1 - (cell12360 ⟨20,by decide⟩).lower)
        (by norm_num [cell12360]) (by norm_num [cell12360])
      exact ⟨E.1,E.2.trans (by norm_num [cell12360])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy21 (n := 12360) (by norm_num)
        (q := 1 - (cell12360 ⟨21,by decide⟩).lower)
        (by norm_num [cell12360]) (by norm_num [cell12360])
      exact ⟨E.1,E.2.trans (by norm_num [cell12360])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy22 (n := 12360) (by norm_num)
        (q := 1 - (cell12360 ⟨22,by decide⟩).lower)
        (by norm_num [cell12360]) (by norm_num [cell12360])
      exact ⟨E.1,E.2.trans (by norm_num [cell12360])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy23 (n := 12360) (by norm_num)
        (q := 1 - (cell12360 ⟨23,by decide⟩).lower)
        (by norm_num [cell12360]) (by norm_num [cell12360])
      exact ⟨E.1,E.2.trans (by norm_num [cell12360])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy24 (n := 12360) (by norm_num)
        (q := 1 - (cell12360 ⟨24,by decide⟩).lower)
        (by norm_num [cell12360]) (by norm_num [cell12360])
      exact ⟨E.1,E.2.trans (by norm_num [cell12360])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy25 (n := 12360) (by norm_num)
        (q := 1 - (cell12360 ⟨25,by decide⟩).lower)
        (by norm_num [cell12360]) (by norm_num [cell12360])
      exact ⟨E.1,E.2.trans (by norm_num [cell12360])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy26 (n := 12360) (by norm_num)
        (q := 1 - (cell12360 ⟨26,by decide⟩).lower)
        (by norm_num [cell12360]) (by norm_num [cell12360])
      exact ⟨E.1,E.2.trans (by norm_num [cell12360])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy27 (n := 12360) (by norm_num)
        (q := 1 - (cell12360 ⟨27,by decide⟩).lower)
        (by norm_num [cell12360]) (by norm_num [cell12360])
      exact ⟨E.1,E.2.trans (by norm_num [cell12360])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy28 (n := 12360) (by norm_num)
        (q := 1 - (cell12360 ⟨28,by decide⟩).lower)
        (by norm_num [cell12360]) (by norm_num [cell12360])
      exact ⟨E.1,E.2.trans (by norm_num [cell12360])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy29 (n := 12360) (by norm_num)
        (q := 1 - (cell12360 ⟨29,by decide⟩).lower)
        (by norm_num [cell12360]) (by norm_num [cell12360])
      exact ⟨E.1,E.2.trans (by norm_num [cell12360])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy30 (n := 12360) (by norm_num)
        (q := 1 - (cell12360 ⟨30,by decide⟩).lower)
        (by norm_num [cell12360]) (by norm_num [cell12360])
      exact ⟨E.1,E.2.trans (by norm_num [cell12360])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy31 (n := 12360) (by norm_num)
        (q := 1 - (cell12360 ⟨31,by decide⟩).lower)
        (by norm_num [cell12360]) (by norm_num [cell12360])
      exact ⟨E.1,E.2.trans (by norm_num [cell12360])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy32 (n := 12360) (by norm_num)
        (q := 1 - (cell12360 ⟨32,by decide⟩).lower)
        (by norm_num [cell12360]) (by norm_num [cell12360])
      exact ⟨E.1,E.2.trans (by norm_num [cell12360])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy33 (n := 12360) (by norm_num)
        (q := 1 - (cell12360 ⟨33,by decide⟩).lower)
        (by norm_num [cell12360]) (by norm_num [cell12360])
      exact ⟨E.1,E.2.trans (by norm_num [cell12360])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy34 (n := 12360) (by norm_num)
        (q := 1 - (cell12360 ⟨34,by decide⟩).lower)
        (by norm_num [cell12360]) (by norm_num [cell12360])
      exact ⟨E.1,E.2.trans (by norm_num [cell12360])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy35 (n := 12360) (by norm_num)
        (q := 1 - (cell12360 ⟨35,by decide⟩).lower)
        (by norm_num [cell12360]) (by norm_num [cell12360])
      exact ⟨E.1,E.2.trans (by norm_num [cell12360])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy36 (n := 12360) (by norm_num)
        (q := 1 - (cell12360 ⟨36,by decide⟩).lower)
        (by norm_num [cell12360]) (by norm_num [cell12360])
      exact ⟨E.1,E.2.trans (by norm_num [cell12360])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy37 (n := 12360) (by norm_num)
        (q := 1 - (cell12360 ⟨37,by decide⟩).lower)
        (by norm_num [cell12360]) (by norm_num [cell12360])
      exact ⟨E.1,E.2.trans (by norm_num [cell12360])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy38 (n := 12360) (by norm_num)
        (q := 1 - (cell12360 ⟨38,by decide⟩).lower)
        (by norm_num [cell12360]) (by norm_num [cell12360])
      exact ⟨E.1,E.2.trans (by norm_num [cell12360])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy39 (n := 12360) (by norm_num)
        (q := 1 - (cell12360 ⟨39,by decide⟩).lower)
        (by norm_num [cell12360]) (by norm_num [cell12360])
      exact ⟨E.1,E.2.trans (by norm_num [cell12360])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy40 (n := 12360) (by norm_num)
        (q := 1 - (cell12360 ⟨40,by decide⟩).lower)
        (by norm_num [cell12360]) (by norm_num [cell12360])
      exact ⟨E.1,E.2.trans (by norm_num [cell12360])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy41 (n := 12360) (by norm_num)
        (q := 1 - (cell12360 ⟨41,by decide⟩).lower)
        (by norm_num [cell12360]) (by norm_num [cell12360])
      exact ⟨E.1,E.2.trans (by norm_num [cell12360])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy42 (n := 12360) (by norm_num)
        (q := 1 - (cell12360 ⟨42,by decide⟩).lower)
        (by norm_num [cell12360]) (by norm_num [cell12360])
      exact ⟨E.1,E.2.trans (by norm_num [cell12360])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy43 (n := 12360) (by norm_num)
        (q := 1 - (cell12360 ⟨43,by decide⟩).lower)
        (by norm_num [cell12360]) (by norm_num [cell12360])
      exact ⟨E.1,E.2.trans (by norm_num [cell12360])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy44 (n := 12360) (by norm_num)
        (q := 1 - (cell12360 ⟨44,by decide⟩).lower)
        (by norm_num [cell12360]) (by norm_num [cell12360])
      exact ⟨E.1,E.2.trans (by norm_num [cell12360])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy45 (n := 12360) (by norm_num)
        (q := 1 - (cell12360 ⟨45,by decide⟩).lower)
        (by norm_num [cell12360]) (by norm_num [cell12360])
      exact ⟨E.1,E.2.trans (by norm_num [cell12360])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy46 (n := 12360) (by norm_num)
        (q := 1 - (cell12360 ⟨46,by decide⟩).lower)
        (by norm_num [cell12360]) (by norm_num [cell12360])
      exact ⟨E.1,E.2.trans (by norm_num [cell12360])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy47 (n := 12360) (by norm_num)
        (q := 1 - (cell12360 ⟨47,by decide⟩).lower)
        (by norm_num [cell12360]) (by norm_num [cell12360])
      exact ⟨E.1,E.2.trans (by norm_num [cell12360])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy48 (n := 12360) (by norm_num)
        (q := 1 - (cell12360 ⟨48,by decide⟩).lower)
        (by norm_num [cell12360]) (by norm_num [cell12360])
      exact ⟨E.1,E.2.trans (by norm_num [cell12360])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy49 (n := 12360) (by norm_num)
        (q := 1 - (cell12360 ⟨49,by decide⟩).lower)
        (by norm_num [cell12360]) (by norm_num [cell12360])
      exact ⟨E.1,E.2.trans (by norm_num [cell12360])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy50 (n := 12360) (by norm_num)
        (q := 1 - (cell12360 ⟨50,by decide⟩).lower)
        (by norm_num [cell12360]) (by norm_num [cell12360])
      exact ⟨E.1,E.2.trans (by norm_num [cell12360])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy51 (n := 12360) (by norm_num)
        (q := 1 - (cell12360 ⟨51,by decide⟩).lower)
        (by norm_num [cell12360]) (by norm_num [cell12360])
      exact ⟨E.1,E.2.trans (by norm_num [cell12360])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy52 (n := 12360) (by norm_num)
        (q := 1 - (cell12360 ⟨52,by decide⟩).lower)
        (by norm_num [cell12360]) (by norm_num [cell12360])
      exact ⟨E.1,E.2.trans (by norm_num [cell12360])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12360

/-! Source-cell containment and simple scalar guards at 12360. -/
namespace BstLean.Part269.N12360
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12360)
open BstLean.Part268 (cell12360)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12360 ⟨10,by decide⟩).lower ∧ (cell12360 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12360 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12360 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12360 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12360 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12360 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12360,cell12360,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12360 ⟨11,by decide⟩).lower ∧ (cell12360 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12360 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12360 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12360 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12360 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12360 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12360,cell12360,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12360 ⟨12,by decide⟩).lower ∧ (cell12360 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12360 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12360 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12360 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12360 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12360 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12360,cell12360,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12360 ⟨13,by decide⟩).lower ∧ (cell12360 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12360 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12360 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12360 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12360 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12360 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12360,cell12360,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12360 ⟨14,by decide⟩).lower ∧ (cell12360 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12360 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12360 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12360 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12360 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12360 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12360,cell12360,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12360 ⟨15,by decide⟩).lower ∧ (cell12360 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12360 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12360 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12360 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12360 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12360 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12360,cell12360,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12360 ⟨16,by decide⟩).lower ∧ (cell12360 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12360 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12360 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12360 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12360 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12360 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12360,cell12360,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12360 ⟨17,by decide⟩).lower ∧ (cell12360 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12360 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12360 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12360 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12360 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12360 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12360,cell12360,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12360 ⟨18,by decide⟩).lower ∧ (cell12360 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12360 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12360 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12360 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12360 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12360 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12360,cell12360,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12360 ⟨19,by decide⟩).lower ∧ (cell12360 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12360 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12360 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12360 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12360 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12360 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12360,cell12360,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12360 ⟨20,by decide⟩).lower ∧ (cell12360 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12360 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12360 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12360 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12360 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12360 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12360,cell12360,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12360 ⟨21,by decide⟩).lower ∧ (cell12360 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12360 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12360 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12360 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12360 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12360 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12360,cell12360,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12360 ⟨22,by decide⟩).lower ∧ (cell12360 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12360 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12360 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12360 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12360 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12360 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12360,cell12360,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12360 ⟨23,by decide⟩).lower ∧ (cell12360 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12360 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12360 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12360 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12360 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12360 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12360,cell12360,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12360 ⟨24,by decide⟩).lower ∧ (cell12360 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12360 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12360 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12360 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12360 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12360 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12360,cell12360,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12360 ⟨25,by decide⟩).lower ∧ (cell12360 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12360 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12360 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12360 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12360 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12360 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12360,cell12360,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12360 ⟨26,by decide⟩).lower ∧ (cell12360 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12360 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12360 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12360 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12360 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12360 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12360,cell12360,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12360 ⟨27,by decide⟩).lower ∧ (cell12360 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12360 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12360 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12360 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12360 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12360 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12360,cell12360,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12360 ⟨28,by decide⟩).lower ∧ (cell12360 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12360 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12360 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12360 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12360 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12360 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12360,cell12360,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12360 ⟨29,by decide⟩).lower ∧ (cell12360 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12360 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12360 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12360 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12360 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12360 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12360,cell12360,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12360 ⟨30,by decide⟩).lower ∧ (cell12360 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12360 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12360 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12360 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12360 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12360 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12360,cell12360,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12360 ⟨31,by decide⟩).lower ∧ (cell12360 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12360 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12360 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12360 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12360 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12360 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12360,cell12360,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12360 ⟨32,by decide⟩).lower ∧ (cell12360 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12360 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12360 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12360 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12360 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12360 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12360,cell12360,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12360 ⟨33,by decide⟩).lower ∧ (cell12360 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12360 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12360 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12360 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12360 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12360 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12360,cell12360,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12360 ⟨34,by decide⟩).lower ∧ (cell12360 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12360 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12360 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12360 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12360 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12360 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12360,cell12360,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12360 ⟨35,by decide⟩).lower ∧ (cell12360 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12360 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12360 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12360 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12360 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12360 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12360,cell12360,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12360 ⟨36,by decide⟩).lower ∧ (cell12360 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12360 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12360 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12360 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12360 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12360 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12360,cell12360,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12360 ⟨37,by decide⟩).lower ∧ (cell12360 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12360 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12360 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12360 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12360 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12360 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12360,cell12360,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12360 ⟨38,by decide⟩).lower ∧ (cell12360 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12360 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12360 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12360 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12360 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12360 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12360,cell12360,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12360 ⟨39,by decide⟩).lower ∧ (cell12360 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12360 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12360 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12360 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12360 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12360 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12360,cell12360,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12360 ⟨40,by decide⟩).lower ∧ (cell12360 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12360 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12360 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12360 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12360 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12360 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12360,cell12360,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12360 ⟨41,by decide⟩).lower ∧ (cell12360 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12360 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12360 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12360 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12360 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12360 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12360,cell12360,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12360 ⟨42,by decide⟩).lower ∧ (cell12360 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12360 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12360 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12360 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12360 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12360 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12360,cell12360,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12360 ⟨43,by decide⟩).lower ∧ (cell12360 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12360 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12360 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12360 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12360 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12360 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12360,cell12360,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12360 ⟨44,by decide⟩).lower ∧ (cell12360 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12360 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12360 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12360 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12360 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12360 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12360,cell12360,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12360 ⟨45,by decide⟩).lower ∧ (cell12360 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12360 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12360 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12360 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12360 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12360 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12360,cell12360,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12360 ⟨46,by decide⟩).lower ∧ (cell12360 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12360 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12360 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12360 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12360 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12360 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12360,cell12360,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12360 ⟨47,by decide⟩).lower ∧ (cell12360 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12360 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12360 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12360 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12360 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12360 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12360,cell12360,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12360 ⟨48,by decide⟩).lower ∧ (cell12360 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12360 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12360 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12360 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12360 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12360 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12360,cell12360,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12360 ⟨49,by decide⟩).lower ∧ (cell12360 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12360 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12360 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12360 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12360 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12360 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12360,cell12360,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12360 ⟨50,by decide⟩).lower ∧ (cell12360 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12360 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12360 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12360 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12360 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12360 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12360,cell12360,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12360 ⟨51,by decide⟩).lower ∧ (cell12360 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12360 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12360 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12360 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12360 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12360 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12360,cell12360,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12360 ⟨52,by decide⟩).lower ∧ (cell12360 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12360 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12360 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12360 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12360 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12360 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12360,cell12360,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12360 i).lower ∧
    (cell12360 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12360 i).upper ≤ (0.532 : ℝ) ∧
    (cell12360 i).centre ≤ (0.1 : ℝ) ∧ (cell12360 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12360 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12360 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12360

/-! The local source numeric instances at 12360 have no network premises. -/
namespace BstLean.Part269.N12360
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12360)
open BstLean.Part268 (cell12360)

noncomputable def sourceNumerics12360 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12360 (cell12360 i)
      scalarRow12360.M scalarRow12360.H scalarRow12360.xi := by
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
    energy_allowance := scalarRow12360.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12360]
    centre_nonneg := (scalarRow12360.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D0.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12360])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12360
/-! Actual 12361 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12361
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12361 ≤ (1.036301281184 : ℝ) := by
  have hr : (111.180034178803 : ℝ) ≤ √(12361 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.180034178803 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12361 12361 (11 / 1000) ≤
    (0.008597650981 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12361) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.180034178803 : ℝ) ≤ √(12361 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12361)
  have hdiv : K / √(12361 : ℝ) ≤ K / 111.180034178803 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.180034178803 ≤ (0.008597650981 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12361.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12361 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12361 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12361 := gPlus_lower 12361
end BstLean.Part269.N12361

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12361
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036301281183 : ℝ) ≤ wn 12361 := by
  have hn : √(12361 : ℝ) ≤ 111.180034178804 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12361 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.180034178804 ≤ 2 / √(12361 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000258911630 : ℝ) ≤ rhoBar 12361 BstLean.Part154.csC ∧
    rhoBar 12361 BstLean.Part154.csC ≤ 0.000258912031 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036301281183 : ℝ) / (1.295212 * 12361) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036301281184 : ℝ) / (1.29521 * 12361) := by gcongr
      _ ≤ (0.000258912031 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12361 BstLean.Part154.csC) ≤ 0.001035715160 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12361 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12361 BstLean.Part154.csC) (piBar (rhoBar 12361 BstLean.Part154.csC)) ≤ 0.000197759013 ∧
    cc1 (rhoBar 12361 BstLean.Part154.csC) (piBar (rhoBar 12361 BstLean.Part154.csC)) ≤ 0.000125835320 ∧
    cc2 (rhoBar 12361 BstLean.Part154.csC) ≤ 0.000073048303 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12361 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12361 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12361 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12361 BstLean.Part154.csC * nuR (rhoBar 12361 BstLean.Part154.csC)) ≤ 0.000517840821 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000258912031 : ℝ) * 0.001035715160 := by gcongr
      _ ≤ (0.000517840821 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12361 BstLean.Part154.csC) * nuR (rhoBar 12361 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001035715160 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12361 BstLean.Part154.csC) * rhoBar 12361 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000258912031 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000258912031 / 2 + 0.399 * 0.001035715160 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000197759013 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000517840821 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125835320 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000258912031 / 1.414213562 := by gcongr
      _ ≤ (0.000073048303 : ℝ) := by norm_num

end BstLean.Part269.N12361

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12361
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12361 BstLean.Part154.csC) (piBar (rhoBar 12361 BstLean.Part154.csC)) ≤ 1.68891E-7 := by
  have hr0 : 0 ≤ rhoBar 12361 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12361 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12361 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12361 BstLean.Part154.csC) (piBar (rhoBar 12361 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12361 BstLean.Part154.csC) (piBar (rhoBar 12361 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12361 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000197759013 : ℝ) ^ 2 + 0.000125835320 ^ 2 + 3 * 0.000073048303 ^ 2 +
        2 * 0.797885 * 0.000197759013 * 0.000125835320 + 2 * 0.000197759013 * 0.000073048303 +
        4 * 0.797885 * 0.000125835320 * 0.000073048303 := by gcongr
    _ ≤ (1.68891E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12361 BstLean.Part154.csC Θ ≤ 0.002703964433 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12361 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12361 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12361 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12361 BstLean.Part154.csC) (piBar (rhoBar 12361 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12361 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036301281184 * 1.68891E-7 / (0.000258911630 : ℝ) := by gcongr
    _ ≤ 0.002703964433 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12361 BstLean.Part154.csC Θ ≤ 0.003001624863 + 0.000683248161 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12361 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12361 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12361 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036301281184 : ℝ) * ((2 * Θ * 0.000258912031 +
        (6863 / 10000) * 0.000258912031 * 12361 * 0.001035715160) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003001624863 + 0.000683248161 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12361 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12361 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12361 0.011 Θ ∧ gammaRatio 12361 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12361 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036301281184 : ℝ) * 0.525 / ((1 - 0.011) * 12361) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12361 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12361 0.011 Θ) :=
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
    badAllowance 12361 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12361 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12361 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12361 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12361 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12361 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12361 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12361 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12361 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12361 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12361 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036301281184 : ℝ) * 12361 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12361 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004101624863 + 0.003387212594 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12361

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12361
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12361 BstLean.Part154.csC) (piBar (rhoBar 12361 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12361 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12361 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12361 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12361 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12361 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12361 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12361 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12361 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12361 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12361 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12361 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12361 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12361 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12361 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053206991908 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12361) ≤ 0.010741475211 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12361 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036301281184)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010741475211 + 2 * 0.737676 / 12361) := by gcongr
    _ ≤ (0.053206991908 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12361 12 ≤ 0.0015 := by
  exact BstLean.Part269.S0.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12361

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12361
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560487817263 : ℝ) ≤ plow 12361 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12361) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053386511475)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001419581328) : eMP 12361 0.011 xi bn ≤ 0.001221700408 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12361 : ℝ) * (1 - 0.011))) ≤ 0.000603990560 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001419581328 / (12361 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000603990560 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000603990560 : ℝ) + 3.141593 * 0.053386511475 / (12361 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001221700408 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053386511475)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001419581328) : PiBarMP 12361 12 0.011 xi bn ≤ 0.163471556424 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12361 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037677331753 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.566853079935 : ℝ) ≤ √((12361 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.180034178803 : ℝ) ≤ √(12361 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12361) ≤ 0.125313941174 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037677331753 + 0.053386511475 * 1.772454 / (2 * (110.566853079935 : ℝ))) * (1 + 0.001221700408) +
        8 / (12361 * 111.180034178803) + 0.125313941174 := by gcongr
    _ ≤ (0.163471556424 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053386511475)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001419581328) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284262204953) :
    parallelOracle 12361 0.011 xi bn cd ≤ 0.164492768609 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12361 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12361 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560487817263 : ℝ) ≤ plow 12361 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.180034178803 : ℝ) ≤ √(12361 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284262204953 : ℝ) / (2 * 0.560487817263 * 111.180034178803)) * 0.163471556424 +
        0.284262204953 ^ 2 / (2 * 0.560487817263 * 111.180034178803) := by gcongr
    _ ≤ (0.164492768609 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053386511475) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001419581328)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284262204953) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12361 12361 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560487817263 : ℝ) ≤ plow 12361 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.180034178803 : ℝ) ≤ √(12361 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12361 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12361 Θ 1.22 ≤ 0.011927505778 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.180034178803 := by gcongr <;> linarith
      _ ≤ (0.011927505778 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12361 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12361 12361 0.011 ≤ 0.008597650981 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12361 12361 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12361 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12361 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12361 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12361 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164492768609 + 0.011927505778 + (0.008597650981 : ℝ) *
        (1 + 2 * (0.284262204953 + 0.011927505778) / (0.560487817263 * 111.180034178803))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12361]

end BstLean.Part269.N12361

/-! The original eight local profiles supply actual 12361 moment certificates. -/
namespace BstLean.Part269.N12361
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12361 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12361 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12361 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053386511475 ∧
    0 ≤ bN 12361 BstLean.Part154.csC (groupTheta g) ∧ bN 12361 BstLean.Part154.csC (groupTheta g) ≤ 0.001419581328 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12361 12361 0.011
      (momentAllowance 12361 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12361 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12361 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12361 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12361 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12361 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231055213045 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12361 0.011
      (momentAllowance 12361 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12361 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12361
/-! The actual computed-centre upper energy formula at 12361. -/
namespace BstLean.Part269.N12361
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12361

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12361
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12361)
open BstLean.Part268 (cell12361)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086549148724
  | 2 => 0.087513039622
  | 3 => 0.088478417744
  | 4 => 0.089447451119
  | 5 => 0.090422733642
  | 6 => 0.091407344510
  | 7 => 0.092404912569
  | 8 => 0.093419685505
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12361 12361 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12361 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004104440387 + 0.003390347157 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S0.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12361

/-! Actual upper energy certificates on all 43 source endpoints at 12361. -/
namespace BstLean.Part269.N12361
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12361)
open BstLean.Part268 (cell12361)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12361 (gMinus 12361) (1 - (cell12361 i).lower) ≤ 1 ∧
    energyUpper 12361 (gMinus 12361) (BstLean.Part211.gPlus 12361)
      (finiteEnergy 12361 12361 0.011) (1 - (cell12361 i).lower) ≤
      (cell12361 i).energy := by
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
      have E := BstLean.Part269.S0.uniformEnergy10 (n := 12361) (by norm_num)
        (q := 1 - (cell12361 ⟨10,by decide⟩).lower)
        (by norm_num [cell12361]) (by norm_num [cell12361])
      exact ⟨E.1,E.2.trans (by norm_num [cell12361])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy11 (n := 12361) (by norm_num)
        (q := 1 - (cell12361 ⟨11,by decide⟩).lower)
        (by norm_num [cell12361]) (by norm_num [cell12361])
      exact ⟨E.1,E.2.trans (by norm_num [cell12361])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy12 (n := 12361) (by norm_num)
        (q := 1 - (cell12361 ⟨12,by decide⟩).lower)
        (by norm_num [cell12361]) (by norm_num [cell12361])
      exact ⟨E.1,E.2.trans (by norm_num [cell12361])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy13 (n := 12361) (by norm_num)
        (q := 1 - (cell12361 ⟨13,by decide⟩).lower)
        (by norm_num [cell12361]) (by norm_num [cell12361])
      exact ⟨E.1,E.2.trans (by norm_num [cell12361])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy14 (n := 12361) (by norm_num)
        (q := 1 - (cell12361 ⟨14,by decide⟩).lower)
        (by norm_num [cell12361]) (by norm_num [cell12361])
      exact ⟨E.1,E.2.trans (by norm_num [cell12361])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy15 (n := 12361) (by norm_num)
        (q := 1 - (cell12361 ⟨15,by decide⟩).lower)
        (by norm_num [cell12361]) (by norm_num [cell12361])
      exact ⟨E.1,E.2.trans (by norm_num [cell12361])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy16 (n := 12361) (by norm_num)
        (q := 1 - (cell12361 ⟨16,by decide⟩).lower)
        (by norm_num [cell12361]) (by norm_num [cell12361])
      exact ⟨E.1,E.2.trans (by norm_num [cell12361])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy17 (n := 12361) (by norm_num)
        (q := 1 - (cell12361 ⟨17,by decide⟩).lower)
        (by norm_num [cell12361]) (by norm_num [cell12361])
      exact ⟨E.1,E.2.trans (by norm_num [cell12361])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy18 (n := 12361) (by norm_num)
        (q := 1 - (cell12361 ⟨18,by decide⟩).lower)
        (by norm_num [cell12361]) (by norm_num [cell12361])
      exact ⟨E.1,E.2.trans (by norm_num [cell12361])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy19 (n := 12361) (by norm_num)
        (q := 1 - (cell12361 ⟨19,by decide⟩).lower)
        (by norm_num [cell12361]) (by norm_num [cell12361])
      exact ⟨E.1,E.2.trans (by norm_num [cell12361])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy20 (n := 12361) (by norm_num)
        (q := 1 - (cell12361 ⟨20,by decide⟩).lower)
        (by norm_num [cell12361]) (by norm_num [cell12361])
      exact ⟨E.1,E.2.trans (by norm_num [cell12361])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy21 (n := 12361) (by norm_num)
        (q := 1 - (cell12361 ⟨21,by decide⟩).lower)
        (by norm_num [cell12361]) (by norm_num [cell12361])
      exact ⟨E.1,E.2.trans (by norm_num [cell12361])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy22 (n := 12361) (by norm_num)
        (q := 1 - (cell12361 ⟨22,by decide⟩).lower)
        (by norm_num [cell12361]) (by norm_num [cell12361])
      exact ⟨E.1,E.2.trans (by norm_num [cell12361])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy23 (n := 12361) (by norm_num)
        (q := 1 - (cell12361 ⟨23,by decide⟩).lower)
        (by norm_num [cell12361]) (by norm_num [cell12361])
      exact ⟨E.1,E.2.trans (by norm_num [cell12361])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy24 (n := 12361) (by norm_num)
        (q := 1 - (cell12361 ⟨24,by decide⟩).lower)
        (by norm_num [cell12361]) (by norm_num [cell12361])
      exact ⟨E.1,E.2.trans (by norm_num [cell12361])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy25 (n := 12361) (by norm_num)
        (q := 1 - (cell12361 ⟨25,by decide⟩).lower)
        (by norm_num [cell12361]) (by norm_num [cell12361])
      exact ⟨E.1,E.2.trans (by norm_num [cell12361])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy26 (n := 12361) (by norm_num)
        (q := 1 - (cell12361 ⟨26,by decide⟩).lower)
        (by norm_num [cell12361]) (by norm_num [cell12361])
      exact ⟨E.1,E.2.trans (by norm_num [cell12361])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy27 (n := 12361) (by norm_num)
        (q := 1 - (cell12361 ⟨27,by decide⟩).lower)
        (by norm_num [cell12361]) (by norm_num [cell12361])
      exact ⟨E.1,E.2.trans (by norm_num [cell12361])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy28 (n := 12361) (by norm_num)
        (q := 1 - (cell12361 ⟨28,by decide⟩).lower)
        (by norm_num [cell12361]) (by norm_num [cell12361])
      exact ⟨E.1,E.2.trans (by norm_num [cell12361])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy29 (n := 12361) (by norm_num)
        (q := 1 - (cell12361 ⟨29,by decide⟩).lower)
        (by norm_num [cell12361]) (by norm_num [cell12361])
      exact ⟨E.1,E.2.trans (by norm_num [cell12361])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy30 (n := 12361) (by norm_num)
        (q := 1 - (cell12361 ⟨30,by decide⟩).lower)
        (by norm_num [cell12361]) (by norm_num [cell12361])
      exact ⟨E.1,E.2.trans (by norm_num [cell12361])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy31 (n := 12361) (by norm_num)
        (q := 1 - (cell12361 ⟨31,by decide⟩).lower)
        (by norm_num [cell12361]) (by norm_num [cell12361])
      exact ⟨E.1,E.2.trans (by norm_num [cell12361])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy32 (n := 12361) (by norm_num)
        (q := 1 - (cell12361 ⟨32,by decide⟩).lower)
        (by norm_num [cell12361]) (by norm_num [cell12361])
      exact ⟨E.1,E.2.trans (by norm_num [cell12361])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy33 (n := 12361) (by norm_num)
        (q := 1 - (cell12361 ⟨33,by decide⟩).lower)
        (by norm_num [cell12361]) (by norm_num [cell12361])
      exact ⟨E.1,E.2.trans (by norm_num [cell12361])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy34 (n := 12361) (by norm_num)
        (q := 1 - (cell12361 ⟨34,by decide⟩).lower)
        (by norm_num [cell12361]) (by norm_num [cell12361])
      exact ⟨E.1,E.2.trans (by norm_num [cell12361])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy35 (n := 12361) (by norm_num)
        (q := 1 - (cell12361 ⟨35,by decide⟩).lower)
        (by norm_num [cell12361]) (by norm_num [cell12361])
      exact ⟨E.1,E.2.trans (by norm_num [cell12361])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy36 (n := 12361) (by norm_num)
        (q := 1 - (cell12361 ⟨36,by decide⟩).lower)
        (by norm_num [cell12361]) (by norm_num [cell12361])
      exact ⟨E.1,E.2.trans (by norm_num [cell12361])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy37 (n := 12361) (by norm_num)
        (q := 1 - (cell12361 ⟨37,by decide⟩).lower)
        (by norm_num [cell12361]) (by norm_num [cell12361])
      exact ⟨E.1,E.2.trans (by norm_num [cell12361])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy38 (n := 12361) (by norm_num)
        (q := 1 - (cell12361 ⟨38,by decide⟩).lower)
        (by norm_num [cell12361]) (by norm_num [cell12361])
      exact ⟨E.1,E.2.trans (by norm_num [cell12361])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy39 (n := 12361) (by norm_num)
        (q := 1 - (cell12361 ⟨39,by decide⟩).lower)
        (by norm_num [cell12361]) (by norm_num [cell12361])
      exact ⟨E.1,E.2.trans (by norm_num [cell12361])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy40 (n := 12361) (by norm_num)
        (q := 1 - (cell12361 ⟨40,by decide⟩).lower)
        (by norm_num [cell12361]) (by norm_num [cell12361])
      exact ⟨E.1,E.2.trans (by norm_num [cell12361])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy41 (n := 12361) (by norm_num)
        (q := 1 - (cell12361 ⟨41,by decide⟩).lower)
        (by norm_num [cell12361]) (by norm_num [cell12361])
      exact ⟨E.1,E.2.trans (by norm_num [cell12361])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy42 (n := 12361) (by norm_num)
        (q := 1 - (cell12361 ⟨42,by decide⟩).lower)
        (by norm_num [cell12361]) (by norm_num [cell12361])
      exact ⟨E.1,E.2.trans (by norm_num [cell12361])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy43 (n := 12361) (by norm_num)
        (q := 1 - (cell12361 ⟨43,by decide⟩).lower)
        (by norm_num [cell12361]) (by norm_num [cell12361])
      exact ⟨E.1,E.2.trans (by norm_num [cell12361])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy44 (n := 12361) (by norm_num)
        (q := 1 - (cell12361 ⟨44,by decide⟩).lower)
        (by norm_num [cell12361]) (by norm_num [cell12361])
      exact ⟨E.1,E.2.trans (by norm_num [cell12361])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy45 (n := 12361) (by norm_num)
        (q := 1 - (cell12361 ⟨45,by decide⟩).lower)
        (by norm_num [cell12361]) (by norm_num [cell12361])
      exact ⟨E.1,E.2.trans (by norm_num [cell12361])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy46 (n := 12361) (by norm_num)
        (q := 1 - (cell12361 ⟨46,by decide⟩).lower)
        (by norm_num [cell12361]) (by norm_num [cell12361])
      exact ⟨E.1,E.2.trans (by norm_num [cell12361])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy47 (n := 12361) (by norm_num)
        (q := 1 - (cell12361 ⟨47,by decide⟩).lower)
        (by norm_num [cell12361]) (by norm_num [cell12361])
      exact ⟨E.1,E.2.trans (by norm_num [cell12361])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy48 (n := 12361) (by norm_num)
        (q := 1 - (cell12361 ⟨48,by decide⟩).lower)
        (by norm_num [cell12361]) (by norm_num [cell12361])
      exact ⟨E.1,E.2.trans (by norm_num [cell12361])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy49 (n := 12361) (by norm_num)
        (q := 1 - (cell12361 ⟨49,by decide⟩).lower)
        (by norm_num [cell12361]) (by norm_num [cell12361])
      exact ⟨E.1,E.2.trans (by norm_num [cell12361])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy50 (n := 12361) (by norm_num)
        (q := 1 - (cell12361 ⟨50,by decide⟩).lower)
        (by norm_num [cell12361]) (by norm_num [cell12361])
      exact ⟨E.1,E.2.trans (by norm_num [cell12361])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy51 (n := 12361) (by norm_num)
        (q := 1 - (cell12361 ⟨51,by decide⟩).lower)
        (by norm_num [cell12361]) (by norm_num [cell12361])
      exact ⟨E.1,E.2.trans (by norm_num [cell12361])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy52 (n := 12361) (by norm_num)
        (q := 1 - (cell12361 ⟨52,by decide⟩).lower)
        (by norm_num [cell12361]) (by norm_num [cell12361])
      exact ⟨E.1,E.2.trans (by norm_num [cell12361])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12361

/-! Source-cell containment and simple scalar guards at 12361. -/
namespace BstLean.Part269.N12361
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12361)
open BstLean.Part268 (cell12361)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12361 ⟨10,by decide⟩).lower ∧ (cell12361 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12361 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12361 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12361 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12361 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12361 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12361,cell12361,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12361 ⟨11,by decide⟩).lower ∧ (cell12361 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12361 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12361 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12361 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12361 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12361 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12361,cell12361,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12361 ⟨12,by decide⟩).lower ∧ (cell12361 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12361 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12361 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12361 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12361 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12361 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12361,cell12361,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12361 ⟨13,by decide⟩).lower ∧ (cell12361 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12361 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12361 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12361 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12361 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12361 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12361,cell12361,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12361 ⟨14,by decide⟩).lower ∧ (cell12361 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12361 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12361 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12361 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12361 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12361 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12361,cell12361,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12361 ⟨15,by decide⟩).lower ∧ (cell12361 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12361 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12361 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12361 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12361 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12361 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12361,cell12361,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12361 ⟨16,by decide⟩).lower ∧ (cell12361 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12361 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12361 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12361 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12361 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12361 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12361,cell12361,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12361 ⟨17,by decide⟩).lower ∧ (cell12361 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12361 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12361 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12361 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12361 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12361 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12361,cell12361,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12361 ⟨18,by decide⟩).lower ∧ (cell12361 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12361 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12361 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12361 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12361 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12361 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12361,cell12361,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12361 ⟨19,by decide⟩).lower ∧ (cell12361 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12361 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12361 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12361 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12361 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12361 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12361,cell12361,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12361 ⟨20,by decide⟩).lower ∧ (cell12361 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12361 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12361 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12361 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12361 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12361 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12361,cell12361,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12361 ⟨21,by decide⟩).lower ∧ (cell12361 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12361 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12361 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12361 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12361 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12361 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12361,cell12361,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12361 ⟨22,by decide⟩).lower ∧ (cell12361 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12361 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12361 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12361 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12361 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12361 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12361,cell12361,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12361 ⟨23,by decide⟩).lower ∧ (cell12361 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12361 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12361 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12361 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12361 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12361 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12361,cell12361,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12361 ⟨24,by decide⟩).lower ∧ (cell12361 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12361 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12361 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12361 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12361 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12361 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12361,cell12361,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12361 ⟨25,by decide⟩).lower ∧ (cell12361 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12361 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12361 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12361 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12361 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12361 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12361,cell12361,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12361 ⟨26,by decide⟩).lower ∧ (cell12361 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12361 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12361 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12361 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12361 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12361 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12361,cell12361,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12361 ⟨27,by decide⟩).lower ∧ (cell12361 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12361 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12361 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12361 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12361 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12361 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12361,cell12361,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12361 ⟨28,by decide⟩).lower ∧ (cell12361 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12361 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12361 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12361 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12361 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12361 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12361,cell12361,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12361 ⟨29,by decide⟩).lower ∧ (cell12361 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12361 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12361 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12361 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12361 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12361 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12361,cell12361,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12361 ⟨30,by decide⟩).lower ∧ (cell12361 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12361 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12361 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12361 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12361 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12361 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12361,cell12361,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12361 ⟨31,by decide⟩).lower ∧ (cell12361 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12361 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12361 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12361 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12361 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12361 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12361,cell12361,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12361 ⟨32,by decide⟩).lower ∧ (cell12361 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12361 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12361 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12361 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12361 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12361 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12361,cell12361,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12361 ⟨33,by decide⟩).lower ∧ (cell12361 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12361 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12361 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12361 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12361 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12361 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12361,cell12361,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12361 ⟨34,by decide⟩).lower ∧ (cell12361 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12361 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12361 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12361 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12361 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12361 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12361,cell12361,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12361 ⟨35,by decide⟩).lower ∧ (cell12361 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12361 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12361 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12361 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12361 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12361 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12361,cell12361,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12361 ⟨36,by decide⟩).lower ∧ (cell12361 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12361 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12361 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12361 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12361 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12361 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12361,cell12361,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12361 ⟨37,by decide⟩).lower ∧ (cell12361 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12361 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12361 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12361 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12361 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12361 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12361,cell12361,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12361 ⟨38,by decide⟩).lower ∧ (cell12361 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12361 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12361 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12361 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12361 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12361 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12361,cell12361,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12361 ⟨39,by decide⟩).lower ∧ (cell12361 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12361 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12361 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12361 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12361 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12361 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12361,cell12361,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12361 ⟨40,by decide⟩).lower ∧ (cell12361 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12361 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12361 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12361 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12361 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12361 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12361,cell12361,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12361 ⟨41,by decide⟩).lower ∧ (cell12361 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12361 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12361 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12361 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12361 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12361 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12361,cell12361,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12361 ⟨42,by decide⟩).lower ∧ (cell12361 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12361 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12361 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12361 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12361 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12361 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12361,cell12361,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12361 ⟨43,by decide⟩).lower ∧ (cell12361 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12361 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12361 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12361 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12361 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12361 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12361,cell12361,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12361 ⟨44,by decide⟩).lower ∧ (cell12361 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12361 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12361 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12361 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12361 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12361 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12361,cell12361,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12361 ⟨45,by decide⟩).lower ∧ (cell12361 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12361 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12361 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12361 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12361 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12361 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12361,cell12361,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12361 ⟨46,by decide⟩).lower ∧ (cell12361 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12361 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12361 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12361 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12361 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12361 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12361,cell12361,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12361 ⟨47,by decide⟩).lower ∧ (cell12361 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12361 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12361 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12361 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12361 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12361 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12361,cell12361,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12361 ⟨48,by decide⟩).lower ∧ (cell12361 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12361 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12361 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12361 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12361 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12361 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12361,cell12361,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12361 ⟨49,by decide⟩).lower ∧ (cell12361 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12361 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12361 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12361 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12361 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12361 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12361,cell12361,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12361 ⟨50,by decide⟩).lower ∧ (cell12361 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12361 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12361 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12361 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12361 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12361 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12361,cell12361,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12361 ⟨51,by decide⟩).lower ∧ (cell12361 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12361 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12361 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12361 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12361 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12361 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12361,cell12361,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12361 ⟨52,by decide⟩).lower ∧ (cell12361 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12361 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12361 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12361 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12361 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12361 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12361,cell12361,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12361 i).lower ∧
    (cell12361 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12361 i).upper ≤ (0.532 : ℝ) ∧
    (cell12361 i).centre ≤ (0.1 : ℝ) ∧ (cell12361 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12361 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12361 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12361

/-! The local source numeric instances at 12361 have no network premises. -/
namespace BstLean.Part269.N12361
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12361)
open BstLean.Part268 (cell12361)

noncomputable def sourceNumerics12361 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12361 (cell12361 i)
      scalarRow12361.M scalarRow12361.H scalarRow12361.xi := by
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
    energy_allowance := scalarRow12361.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12361]
    centre_nonneg := (scalarRow12361.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D0.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12361])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12361
/-! Actual 12362 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12362
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12362 ≤ (1.036299799806 : ℝ) := by
  have hr : (111.184531298198 : ℝ) ≤ √(12362 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.184531298198 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12362 12362 (11 / 1000) ≤
    (0.008597303226 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12362) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.184531298198 : ℝ) ≤ √(12362 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12362)
  have hdiv : K / √(12362 : ℝ) ≤ K / 111.184531298198 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.184531298198 ≤ (0.008597303226 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12362.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12362 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12362 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12362 := gPlus_lower 12362
end BstLean.Part269.N12362

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12362
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036299799805 : ℝ) ≤ wn 12362 := by
  have hn : √(12362 : ℝ) ≤ 111.184531298199 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12362 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.184531298199 ≤ 2 / √(12362 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000258890316 : ℝ) ≤ rhoBar 12362 BstLean.Part154.csC ∧
    rhoBar 12362 BstLean.Part154.csC ≤ 0.000258890717 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036299799805 : ℝ) / (1.295212 * 12362) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036299799806 : ℝ) / (1.29521 * 12362) := by gcongr
      _ ≤ (0.000258890717 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12362 BstLean.Part154.csC) ≤ 0.001035629893 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12362 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12362 BstLean.Part154.csC) (piBar (rhoBar 12362 BstLean.Part154.csC)) ≤ 0.000197742732 ∧
    cc1 (rhoBar 12362 BstLean.Part154.csC) (piBar (rhoBar 12362 BstLean.Part154.csC)) ≤ 0.000125824961 ∧
    cc2 (rhoBar 12362 BstLean.Part154.csC) ≤ 0.000073042290 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12362 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12362 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12362 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12362 BstLean.Part154.csC * nuR (rhoBar 12362 BstLean.Part154.csC)) ≤ 0.000517798190 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000258890717 : ℝ) * 0.001035629893 := by gcongr
      _ ≤ (0.000517798190 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12362 BstLean.Part154.csC) * nuR (rhoBar 12362 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001035629893 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12362 BstLean.Part154.csC) * rhoBar 12362 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000258890717 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000258890717 / 2 + 0.399 * 0.001035629893 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000197742732 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000517798190 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125824961 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000258890717 / 1.414213562 := by gcongr
      _ ≤ (0.000073042290 : ℝ) := by norm_num

end BstLean.Part269.N12362

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12362
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12362 BstLean.Part154.csC) (piBar (rhoBar 12362 BstLean.Part154.csC)) ≤ 1.68864E-7 := by
  have hr0 : 0 ≤ rhoBar 12362 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12362 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12362 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12362 BstLean.Part154.csC) (piBar (rhoBar 12362 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12362 BstLean.Part154.csC) (piBar (rhoBar 12362 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12362 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000197742732 : ℝ) ^ 2 + 0.000125824961 ^ 2 + 3 * 0.000073042290 ^ 2 +
        2 * 0.797885 * 0.000197742732 * 0.000125824961 + 2 * 0.000197742732 * 0.000073042290 +
        4 * 0.797885 * 0.000125824961 * 0.000073042290 := by gcongr
    _ ≤ (1.68864E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12362 BstLean.Part154.csC Θ ≤ 0.002703750872 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12362 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12362 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12362 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12362 BstLean.Part154.csC) (piBar (rhoBar 12362 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12362 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036299799806 * 1.68864E-7 / (0.000258890316 : ℝ) := by gcongr
    _ ≤ 0.002703750872 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12362 BstLean.Part154.csC Θ ≤ 0.003001369172 + 0.000683190939 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12362 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12362 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12362 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036299799806 : ℝ) * ((2 * Θ * 0.000258890717 +
        (6863 / 10000) * 0.000258890717 * 12362 * 0.001035629893) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003001369172 + 0.000683190939 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12362 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12362 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12362 0.011 Θ ∧ gammaRatio 12362 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12362 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036299799806 : ℝ) * 0.525 / ((1 - 0.011) * 12362) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12362 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12362 0.011 Θ) :=
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
    badAllowance 12362 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12362 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12362 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12362 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12362 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12362 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12362 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12362 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12362 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12362 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12362 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036299799806 : ℝ) * 12362 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12362 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004101369172 + 0.003386941811 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12362

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12362
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12362 BstLean.Part154.csC) (piBar (rhoBar 12362 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12362 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12362 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12362 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12362 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12362 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12362 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12362 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12362 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12362 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12362 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12362 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12362 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12362 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12362 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053204816178 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12362) ≤ 0.010741040747 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12362 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036299799806)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010741040747 + 2 * 0.737676 / 12362) := by gcongr
    _ ≤ (0.053204816178 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12362 12 ≤ 0.0015 := by
  exact BstLean.Part269.S0.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12362

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12362
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560487864997 : ℝ) ≤ plow 12362 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12362) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053386113623)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001419469208) : eMP 12362 0.011 xi bn ≤ 0.001221602634 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12362 : ℝ) * (1 - 0.011))) ≤ 0.000603942279 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001419469208 / (12362 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000603942279 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000603942279 : ℝ) + 3.141593 * 0.053386113623 / (12362 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001221602634 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053386113623)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001419469208) : PiBarMP 12362 12 0.011 xi bn ≤ 0.163464973109 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12362 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037675843826 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.571325396777 : ℝ) ≤ √((12362 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.184531298198 : ℝ) ≤ √(12362 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12362) ≤ 0.125308872557 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037675843826 + 0.053386113623 * 1.772454 / (2 * (110.571325396777 : ℝ))) * (1 + 0.001221602634) +
        8 / (12362 * 111.184531298198) + 0.125308872557 := by gcongr
    _ ≤ (0.163464973109 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053386113623)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001419469208) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284259168276) :
    parallelOracle 12362 0.011 xi bn cd ≤ 0.164486111052 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12362 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12362 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560487864997 : ℝ) ≤ plow 12362 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.184531298198 : ℝ) ≤ √(12362 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284259168276 : ℝ) / (2 * 0.560487864997 * 111.184531298198)) * 0.163464973109 +
        0.284259168276 ^ 2 / (2 * 0.560487864997 * 111.184531298198) := by gcongr
    _ ≤ (0.164486111052 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053386113623) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001419469208)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284259168276) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12362 12362 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560487864997 : ℝ) ≤ plow 12362 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.184531298198 : ℝ) ≤ √(12362 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12362 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12362 Θ 1.22 ≤ 0.011927023342 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.184531298198 := by gcongr <;> linarith
      _ ≤ (0.011927023342 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12362 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12362 12362 0.011 ≤ 0.008597303226 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12362 12362 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12362 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12362 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12362 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12362 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164486111052 + 0.011927023342 + (0.008597303226 : ℝ) *
        (1 + 2 * (0.284259168276 + 0.011927023342) / (0.560487864997 * 111.184531298198))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12362]

end BstLean.Part269.N12362

/-! The original eight local profiles supply actual 12362 moment certificates. -/
namespace BstLean.Part269.N12362
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12362 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12362 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12362 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053386113623 ∧
    0 ≤ bN 12362 BstLean.Part154.csC (groupTheta g) ∧ bN 12362 BstLean.Part154.csC (groupTheta g) ≤ 0.001419469208 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12362 12362 0.011
      (momentAllowance 12362 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12362 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12362 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12362 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12362 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12362 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231054352098 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12362 0.011
      (momentAllowance 12362 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12362 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12362
/-! The actual computed-centre upper energy formula at 12362. -/
namespace BstLean.Part269.N12362
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12362

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12362
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12362)
open BstLean.Part268 (cell12362)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086545792319
  | 2 => 0.087509610702
  | 3 => 0.088474904065
  | 4 => 0.089443837758
  | 5 => 0.090419002550
  | 6 => 0.091403474011
  | 7 => 0.092400876808
  | 8 => 0.093415453842
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12362 12362 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12362 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004104440387 + 0.003390347157 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S0.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12362

/-! Actual upper energy certificates on all 43 source endpoints at 12362. -/
namespace BstLean.Part269.N12362
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12362)
open BstLean.Part268 (cell12362)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12362 (gMinus 12362) (1 - (cell12362 i).lower) ≤ 1 ∧
    energyUpper 12362 (gMinus 12362) (BstLean.Part211.gPlus 12362)
      (finiteEnergy 12362 12362 0.011) (1 - (cell12362 i).lower) ≤
      (cell12362 i).energy := by
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
      have E := BstLean.Part269.S0.uniformEnergy10 (n := 12362) (by norm_num)
        (q := 1 - (cell12362 ⟨10,by decide⟩).lower)
        (by norm_num [cell12362]) (by norm_num [cell12362])
      exact ⟨E.1,E.2.trans (by norm_num [cell12362])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy11 (n := 12362) (by norm_num)
        (q := 1 - (cell12362 ⟨11,by decide⟩).lower)
        (by norm_num [cell12362]) (by norm_num [cell12362])
      exact ⟨E.1,E.2.trans (by norm_num [cell12362])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy12 (n := 12362) (by norm_num)
        (q := 1 - (cell12362 ⟨12,by decide⟩).lower)
        (by norm_num [cell12362]) (by norm_num [cell12362])
      exact ⟨E.1,E.2.trans (by norm_num [cell12362])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy13 (n := 12362) (by norm_num)
        (q := 1 - (cell12362 ⟨13,by decide⟩).lower)
        (by norm_num [cell12362]) (by norm_num [cell12362])
      exact ⟨E.1,E.2.trans (by norm_num [cell12362])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy14 (n := 12362) (by norm_num)
        (q := 1 - (cell12362 ⟨14,by decide⟩).lower)
        (by norm_num [cell12362]) (by norm_num [cell12362])
      exact ⟨E.1,E.2.trans (by norm_num [cell12362])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy15 (n := 12362) (by norm_num)
        (q := 1 - (cell12362 ⟨15,by decide⟩).lower)
        (by norm_num [cell12362]) (by norm_num [cell12362])
      exact ⟨E.1,E.2.trans (by norm_num [cell12362])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy16 (n := 12362) (by norm_num)
        (q := 1 - (cell12362 ⟨16,by decide⟩).lower)
        (by norm_num [cell12362]) (by norm_num [cell12362])
      exact ⟨E.1,E.2.trans (by norm_num [cell12362])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy17 (n := 12362) (by norm_num)
        (q := 1 - (cell12362 ⟨17,by decide⟩).lower)
        (by norm_num [cell12362]) (by norm_num [cell12362])
      exact ⟨E.1,E.2.trans (by norm_num [cell12362])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy18 (n := 12362) (by norm_num)
        (q := 1 - (cell12362 ⟨18,by decide⟩).lower)
        (by norm_num [cell12362]) (by norm_num [cell12362])
      exact ⟨E.1,E.2.trans (by norm_num [cell12362])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy19 (n := 12362) (by norm_num)
        (q := 1 - (cell12362 ⟨19,by decide⟩).lower)
        (by norm_num [cell12362]) (by norm_num [cell12362])
      exact ⟨E.1,E.2.trans (by norm_num [cell12362])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy20 (n := 12362) (by norm_num)
        (q := 1 - (cell12362 ⟨20,by decide⟩).lower)
        (by norm_num [cell12362]) (by norm_num [cell12362])
      exact ⟨E.1,E.2.trans (by norm_num [cell12362])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy21 (n := 12362) (by norm_num)
        (q := 1 - (cell12362 ⟨21,by decide⟩).lower)
        (by norm_num [cell12362]) (by norm_num [cell12362])
      exact ⟨E.1,E.2.trans (by norm_num [cell12362])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy22 (n := 12362) (by norm_num)
        (q := 1 - (cell12362 ⟨22,by decide⟩).lower)
        (by norm_num [cell12362]) (by norm_num [cell12362])
      exact ⟨E.1,E.2.trans (by norm_num [cell12362])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy23 (n := 12362) (by norm_num)
        (q := 1 - (cell12362 ⟨23,by decide⟩).lower)
        (by norm_num [cell12362]) (by norm_num [cell12362])
      exact ⟨E.1,E.2.trans (by norm_num [cell12362])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy24 (n := 12362) (by norm_num)
        (q := 1 - (cell12362 ⟨24,by decide⟩).lower)
        (by norm_num [cell12362]) (by norm_num [cell12362])
      exact ⟨E.1,E.2.trans (by norm_num [cell12362])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy25 (n := 12362) (by norm_num)
        (q := 1 - (cell12362 ⟨25,by decide⟩).lower)
        (by norm_num [cell12362]) (by norm_num [cell12362])
      exact ⟨E.1,E.2.trans (by norm_num [cell12362])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy26 (n := 12362) (by norm_num)
        (q := 1 - (cell12362 ⟨26,by decide⟩).lower)
        (by norm_num [cell12362]) (by norm_num [cell12362])
      exact ⟨E.1,E.2.trans (by norm_num [cell12362])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy27 (n := 12362) (by norm_num)
        (q := 1 - (cell12362 ⟨27,by decide⟩).lower)
        (by norm_num [cell12362]) (by norm_num [cell12362])
      exact ⟨E.1,E.2.trans (by norm_num [cell12362])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy28 (n := 12362) (by norm_num)
        (q := 1 - (cell12362 ⟨28,by decide⟩).lower)
        (by norm_num [cell12362]) (by norm_num [cell12362])
      exact ⟨E.1,E.2.trans (by norm_num [cell12362])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy29 (n := 12362) (by norm_num)
        (q := 1 - (cell12362 ⟨29,by decide⟩).lower)
        (by norm_num [cell12362]) (by norm_num [cell12362])
      exact ⟨E.1,E.2.trans (by norm_num [cell12362])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy30 (n := 12362) (by norm_num)
        (q := 1 - (cell12362 ⟨30,by decide⟩).lower)
        (by norm_num [cell12362]) (by norm_num [cell12362])
      exact ⟨E.1,E.2.trans (by norm_num [cell12362])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy31 (n := 12362) (by norm_num)
        (q := 1 - (cell12362 ⟨31,by decide⟩).lower)
        (by norm_num [cell12362]) (by norm_num [cell12362])
      exact ⟨E.1,E.2.trans (by norm_num [cell12362])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy32 (n := 12362) (by norm_num)
        (q := 1 - (cell12362 ⟨32,by decide⟩).lower)
        (by norm_num [cell12362]) (by norm_num [cell12362])
      exact ⟨E.1,E.2.trans (by norm_num [cell12362])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy33 (n := 12362) (by norm_num)
        (q := 1 - (cell12362 ⟨33,by decide⟩).lower)
        (by norm_num [cell12362]) (by norm_num [cell12362])
      exact ⟨E.1,E.2.trans (by norm_num [cell12362])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy34 (n := 12362) (by norm_num)
        (q := 1 - (cell12362 ⟨34,by decide⟩).lower)
        (by norm_num [cell12362]) (by norm_num [cell12362])
      exact ⟨E.1,E.2.trans (by norm_num [cell12362])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy35 (n := 12362) (by norm_num)
        (q := 1 - (cell12362 ⟨35,by decide⟩).lower)
        (by norm_num [cell12362]) (by norm_num [cell12362])
      exact ⟨E.1,E.2.trans (by norm_num [cell12362])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy36 (n := 12362) (by norm_num)
        (q := 1 - (cell12362 ⟨36,by decide⟩).lower)
        (by norm_num [cell12362]) (by norm_num [cell12362])
      exact ⟨E.1,E.2.trans (by norm_num [cell12362])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy37 (n := 12362) (by norm_num)
        (q := 1 - (cell12362 ⟨37,by decide⟩).lower)
        (by norm_num [cell12362]) (by norm_num [cell12362])
      exact ⟨E.1,E.2.trans (by norm_num [cell12362])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy38 (n := 12362) (by norm_num)
        (q := 1 - (cell12362 ⟨38,by decide⟩).lower)
        (by norm_num [cell12362]) (by norm_num [cell12362])
      exact ⟨E.1,E.2.trans (by norm_num [cell12362])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy39 (n := 12362) (by norm_num)
        (q := 1 - (cell12362 ⟨39,by decide⟩).lower)
        (by norm_num [cell12362]) (by norm_num [cell12362])
      exact ⟨E.1,E.2.trans (by norm_num [cell12362])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy40 (n := 12362) (by norm_num)
        (q := 1 - (cell12362 ⟨40,by decide⟩).lower)
        (by norm_num [cell12362]) (by norm_num [cell12362])
      exact ⟨E.1,E.2.trans (by norm_num [cell12362])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy41 (n := 12362) (by norm_num)
        (q := 1 - (cell12362 ⟨41,by decide⟩).lower)
        (by norm_num [cell12362]) (by norm_num [cell12362])
      exact ⟨E.1,E.2.trans (by norm_num [cell12362])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy42 (n := 12362) (by norm_num)
        (q := 1 - (cell12362 ⟨42,by decide⟩).lower)
        (by norm_num [cell12362]) (by norm_num [cell12362])
      exact ⟨E.1,E.2.trans (by norm_num [cell12362])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy43 (n := 12362) (by norm_num)
        (q := 1 - (cell12362 ⟨43,by decide⟩).lower)
        (by norm_num [cell12362]) (by norm_num [cell12362])
      exact ⟨E.1,E.2.trans (by norm_num [cell12362])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy44 (n := 12362) (by norm_num)
        (q := 1 - (cell12362 ⟨44,by decide⟩).lower)
        (by norm_num [cell12362]) (by norm_num [cell12362])
      exact ⟨E.1,E.2.trans (by norm_num [cell12362])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy45 (n := 12362) (by norm_num)
        (q := 1 - (cell12362 ⟨45,by decide⟩).lower)
        (by norm_num [cell12362]) (by norm_num [cell12362])
      exact ⟨E.1,E.2.trans (by norm_num [cell12362])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy46 (n := 12362) (by norm_num)
        (q := 1 - (cell12362 ⟨46,by decide⟩).lower)
        (by norm_num [cell12362]) (by norm_num [cell12362])
      exact ⟨E.1,E.2.trans (by norm_num [cell12362])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy47 (n := 12362) (by norm_num)
        (q := 1 - (cell12362 ⟨47,by decide⟩).lower)
        (by norm_num [cell12362]) (by norm_num [cell12362])
      exact ⟨E.1,E.2.trans (by norm_num [cell12362])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy48 (n := 12362) (by norm_num)
        (q := 1 - (cell12362 ⟨48,by decide⟩).lower)
        (by norm_num [cell12362]) (by norm_num [cell12362])
      exact ⟨E.1,E.2.trans (by norm_num [cell12362])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy49 (n := 12362) (by norm_num)
        (q := 1 - (cell12362 ⟨49,by decide⟩).lower)
        (by norm_num [cell12362]) (by norm_num [cell12362])
      exact ⟨E.1,E.2.trans (by norm_num [cell12362])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy50 (n := 12362) (by norm_num)
        (q := 1 - (cell12362 ⟨50,by decide⟩).lower)
        (by norm_num [cell12362]) (by norm_num [cell12362])
      exact ⟨E.1,E.2.trans (by norm_num [cell12362])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy51 (n := 12362) (by norm_num)
        (q := 1 - (cell12362 ⟨51,by decide⟩).lower)
        (by norm_num [cell12362]) (by norm_num [cell12362])
      exact ⟨E.1,E.2.trans (by norm_num [cell12362])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy52 (n := 12362) (by norm_num)
        (q := 1 - (cell12362 ⟨52,by decide⟩).lower)
        (by norm_num [cell12362]) (by norm_num [cell12362])
      exact ⟨E.1,E.2.trans (by norm_num [cell12362])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12362

/-! Source-cell containment and simple scalar guards at 12362. -/
namespace BstLean.Part269.N12362
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12362)
open BstLean.Part268 (cell12362)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12362 ⟨10,by decide⟩).lower ∧ (cell12362 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12362 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12362 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12362 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12362 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12362 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12362,cell12362,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12362 ⟨11,by decide⟩).lower ∧ (cell12362 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12362 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12362 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12362 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12362 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12362 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12362,cell12362,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12362 ⟨12,by decide⟩).lower ∧ (cell12362 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12362 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12362 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12362 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12362 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12362 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12362,cell12362,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12362 ⟨13,by decide⟩).lower ∧ (cell12362 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12362 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12362 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12362 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12362 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12362 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12362,cell12362,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12362 ⟨14,by decide⟩).lower ∧ (cell12362 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12362 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12362 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12362 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12362 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12362 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12362,cell12362,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12362 ⟨15,by decide⟩).lower ∧ (cell12362 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12362 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12362 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12362 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12362 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12362 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12362,cell12362,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12362 ⟨16,by decide⟩).lower ∧ (cell12362 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12362 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12362 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12362 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12362 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12362 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12362,cell12362,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12362 ⟨17,by decide⟩).lower ∧ (cell12362 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12362 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12362 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12362 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12362 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12362 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12362,cell12362,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12362 ⟨18,by decide⟩).lower ∧ (cell12362 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12362 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12362 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12362 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12362 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12362 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12362,cell12362,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12362 ⟨19,by decide⟩).lower ∧ (cell12362 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12362 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12362 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12362 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12362 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12362 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12362,cell12362,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12362 ⟨20,by decide⟩).lower ∧ (cell12362 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12362 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12362 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12362 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12362 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12362 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12362,cell12362,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12362 ⟨21,by decide⟩).lower ∧ (cell12362 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12362 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12362 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12362 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12362 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12362 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12362,cell12362,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12362 ⟨22,by decide⟩).lower ∧ (cell12362 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12362 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12362 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12362 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12362 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12362 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12362,cell12362,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12362 ⟨23,by decide⟩).lower ∧ (cell12362 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12362 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12362 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12362 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12362 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12362 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12362,cell12362,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12362 ⟨24,by decide⟩).lower ∧ (cell12362 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12362 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12362 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12362 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12362 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12362 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12362,cell12362,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12362 ⟨25,by decide⟩).lower ∧ (cell12362 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12362 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12362 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12362 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12362 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12362 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12362,cell12362,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12362 ⟨26,by decide⟩).lower ∧ (cell12362 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12362 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12362 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12362 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12362 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12362 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12362,cell12362,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12362 ⟨27,by decide⟩).lower ∧ (cell12362 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12362 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12362 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12362 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12362 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12362 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12362,cell12362,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12362 ⟨28,by decide⟩).lower ∧ (cell12362 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12362 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12362 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12362 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12362 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12362 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12362,cell12362,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12362 ⟨29,by decide⟩).lower ∧ (cell12362 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12362 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12362 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12362 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12362 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12362 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12362,cell12362,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12362 ⟨30,by decide⟩).lower ∧ (cell12362 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12362 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12362 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12362 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12362 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12362 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12362,cell12362,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12362 ⟨31,by decide⟩).lower ∧ (cell12362 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12362 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12362 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12362 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12362 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12362 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12362,cell12362,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12362 ⟨32,by decide⟩).lower ∧ (cell12362 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12362 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12362 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12362 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12362 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12362 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12362,cell12362,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12362 ⟨33,by decide⟩).lower ∧ (cell12362 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12362 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12362 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12362 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12362 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12362 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12362,cell12362,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12362 ⟨34,by decide⟩).lower ∧ (cell12362 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12362 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12362 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12362 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12362 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12362 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12362,cell12362,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12362 ⟨35,by decide⟩).lower ∧ (cell12362 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12362 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12362 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12362 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12362 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12362 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12362,cell12362,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12362 ⟨36,by decide⟩).lower ∧ (cell12362 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12362 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12362 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12362 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12362 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12362 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12362,cell12362,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12362 ⟨37,by decide⟩).lower ∧ (cell12362 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12362 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12362 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12362 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12362 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12362 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12362,cell12362,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12362 ⟨38,by decide⟩).lower ∧ (cell12362 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12362 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12362 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12362 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12362 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12362 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12362,cell12362,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12362 ⟨39,by decide⟩).lower ∧ (cell12362 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12362 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12362 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12362 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12362 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12362 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12362,cell12362,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12362 ⟨40,by decide⟩).lower ∧ (cell12362 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12362 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12362 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12362 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12362 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12362 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12362,cell12362,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12362 ⟨41,by decide⟩).lower ∧ (cell12362 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12362 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12362 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12362 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12362 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12362 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12362,cell12362,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12362 ⟨42,by decide⟩).lower ∧ (cell12362 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12362 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12362 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12362 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12362 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12362 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12362,cell12362,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12362 ⟨43,by decide⟩).lower ∧ (cell12362 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12362 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12362 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12362 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12362 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12362 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12362,cell12362,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12362 ⟨44,by decide⟩).lower ∧ (cell12362 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12362 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12362 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12362 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12362 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12362 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12362,cell12362,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12362 ⟨45,by decide⟩).lower ∧ (cell12362 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12362 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12362 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12362 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12362 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12362 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12362,cell12362,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12362 ⟨46,by decide⟩).lower ∧ (cell12362 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12362 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12362 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12362 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12362 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12362 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12362,cell12362,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12362 ⟨47,by decide⟩).lower ∧ (cell12362 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12362 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12362 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12362 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12362 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12362 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12362,cell12362,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12362 ⟨48,by decide⟩).lower ∧ (cell12362 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12362 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12362 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12362 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12362 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12362 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12362,cell12362,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12362 ⟨49,by decide⟩).lower ∧ (cell12362 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12362 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12362 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12362 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12362 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12362 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12362,cell12362,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12362 ⟨50,by decide⟩).lower ∧ (cell12362 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12362 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12362 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12362 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12362 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12362 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12362,cell12362,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12362 ⟨51,by decide⟩).lower ∧ (cell12362 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12362 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12362 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12362 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12362 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12362 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12362,cell12362,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12362 ⟨52,by decide⟩).lower ∧ (cell12362 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12362 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12362 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12362 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12362 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12362 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12362,cell12362,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12362 i).lower ∧
    (cell12362 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12362 i).upper ≤ (0.532 : ℝ) ∧
    (cell12362 i).centre ≤ (0.1 : ℝ) ∧ (cell12362 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12362 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12362 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12362

/-! The local source numeric instances at 12362 have no network premises. -/
namespace BstLean.Part269.N12362
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12362)
open BstLean.Part268 (cell12362)

noncomputable def sourceNumerics12362 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12362 (cell12362 i)
      scalarRow12362.M scalarRow12362.H scalarRow12362.xi := by
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
    energy_allowance := scalarRow12362.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12362]
    centre_nonneg := (scalarRow12362.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D0.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12362])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12362
/-! Actual 12363 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12363
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12363 ≤ (1.036298318608 : ℝ) := by
  have hr : (111.189028235703 : ℝ) ≤ √(12363 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.189028235703 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12363 12363 (11 / 1000) ≤
    (0.008596955513 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12363) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.189028235703 : ℝ) ≤ √(12363 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12363)
  have hdiv : K / √(12363 : ℝ) ≤ K / 111.189028235703 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.189028235703 ≤ (0.008596955513 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12363.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12363 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12363 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12363 := gPlus_lower 12363
end BstLean.Part269.N12363

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12363
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036298318607 : ℝ) ≤ wn 12363 := by
  have hn : √(12363 : ℝ) ≤ 111.189028235704 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12363 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.189028235704 ≤ 2 / √(12363 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000258869006 : ℝ) ≤ rhoBar 12363 BstLean.Part154.csC ∧
    rhoBar 12363 BstLean.Part154.csC ≤ 0.000258869406 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036298318607 : ℝ) / (1.295212 * 12363) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036298318608 : ℝ) / (1.29521 * 12363) := by gcongr
      _ ≤ (0.000258869406 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12363 BstLean.Part154.csC) ≤ 0.001035544638 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12363 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12363 BstLean.Part154.csC) (piBar (rhoBar 12363 BstLean.Part154.csC)) ≤ 0.000197726454 ∧
    cc1 (rhoBar 12363 BstLean.Part154.csC) (piBar (rhoBar 12363 BstLean.Part154.csC)) ≤ 0.000125814603 ∧
    cc2 (rhoBar 12363 BstLean.Part154.csC) ≤ 0.000073036277 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12363 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12363 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12363 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12363 BstLean.Part154.csC * nuR (rhoBar 12363 BstLean.Part154.csC)) ≤ 0.000517755566 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000258869406 : ℝ) * 0.001035544638 := by gcongr
      _ ≤ (0.000517755566 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12363 BstLean.Part154.csC) * nuR (rhoBar 12363 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001035544638 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12363 BstLean.Part154.csC) * rhoBar 12363 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000258869406 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000258869406 / 2 + 0.399 * 0.001035544638 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000197726454 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000517755566 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125814603 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000258869406 / 1.414213562 := by gcongr
      _ ≤ (0.000073036277 : ℝ) := by norm_num

end BstLean.Part269.N12363

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12363
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12363 BstLean.Part154.csC) (piBar (rhoBar 12363 BstLean.Part154.csC)) ≤ 1.68836E-7 := by
  have hr0 : 0 ≤ rhoBar 12363 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12363 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12363 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12363 BstLean.Part154.csC) (piBar (rhoBar 12363 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12363 BstLean.Part154.csC) (piBar (rhoBar 12363 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12363 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000197726454 : ℝ) ^ 2 + 0.000125814603 ^ 2 + 3 * 0.000073036277 ^ 2 +
        2 * 0.797885 * 0.000197726454 * 0.000125814603 + 2 * 0.000197726454 * 0.000073036277 +
        4 * 0.797885 * 0.000125814603 * 0.000073036277 := by gcongr
    _ ≤ (1.68836E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12363 BstLean.Part154.csC Θ ≤ 0.002703521223 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12363 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12363 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12363 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12363 BstLean.Part154.csC) (piBar (rhoBar 12363 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12363 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036298318608 * 1.68836E-7 / (0.000258869006 : ℝ) := by gcongr
    _ ≤ 0.002703521223 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12363 BstLean.Part154.csC Θ ≤ 0.003001113512 + 0.000683133724 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12363 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12363 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12363 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036298318608 : ℝ) * ((2 * Θ * 0.000258869406 +
        (6863 / 10000) * 0.000258869406 * 12363 * 0.001035544638) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003001113512 + 0.000683133724 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12363 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12363 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12363 0.011 Θ ∧ gammaRatio 12363 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12363 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036298318608 : ℝ) * 0.525 / ((1 - 0.011) * 12363) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12363 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12363 0.011 Θ) :=
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
    badAllowance 12363 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12363 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12363 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12363 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12363 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12363 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12363 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12363 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12363 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12363 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12363 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036298318608 : ℝ) * 12363 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12363 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004101113512 + 0.003386654947 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12363

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12363
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12363 BstLean.Part154.csC) (piBar (rhoBar 12363 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12363 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12363 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12363 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12363 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12363 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12363 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12363 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12363 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12363 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12363 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12363 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12363 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12363 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12363 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053202640715 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12363) ≤ 0.010740606336 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12363 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036298318608)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010740606336 + 2 * 0.737676 / 12363) := by gcongr
    _ ≤ (0.053202640715 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12363 12 ≤ 0.0015 := by
  exact BstLean.Part269.S0.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12363

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12363
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560487912723 : ℝ) ≤ plow 12363 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12363) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053385707360)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001419348643) : eMP 12363 0.011 xi bn ≤ 0.001221501272 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12363 : ℝ) * (1 - 0.011))) ≤ 0.000603892205 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001419348643 / (12363 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000603892205 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000603892205 : ℝ) + 3.141593 * 0.053385707360 / (12363 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001221501272 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053385707360)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001419348643) : PiBarMP 12363 12 0.011 xi bn ≤ 0.163458277935 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12363 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037674243762 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.575797532733 : ℝ) ≤ √((12363 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.189028235703 : ℝ) ≤ √(12363 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12363) ≤ 0.125303804556 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037674243762 + 0.053385707360 * 1.772454 / (2 * (110.575797532733 : ℝ))) * (1 + 0.001221501272) +
        8 / (12363 * 111.189028235703) + 0.125303804556 := by gcongr
    _ ≤ (0.163458277935 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053385707360)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001419348643) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284256113661) :
    parallelOracle 12363 0.011 xi bn cd ≤ 0.164479341284 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12363 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12363 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560487912723 : ℝ) ≤ plow 12363 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.189028235703 : ℝ) ≤ √(12363 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284256113661 : ℝ) / (2 * 0.560487912723 * 111.189028235703)) * 0.163458277935 +
        0.284256113661 ^ 2 / (2 * 0.560487912723 * 111.189028235703) := by gcongr
    _ ≤ (0.164479341284 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053385707360) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001419348643)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284256113661) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12363 12363 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560487912723 : ℝ) ≤ plow 12363 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.189028235703 : ℝ) ≤ √(12363 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12363 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12363 Θ 1.22 ≤ 0.011926540964 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.189028235703 := by gcongr <;> linarith
      _ ≤ (0.011926540964 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12363 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12363 12363 0.011 ≤ 0.008596955513 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12363 12363 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12363 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12363 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12363 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12363 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164479341284 + 0.011926540964 + (0.008596955513 : ℝ) *
        (1 + 2 * (0.284256113661 + 0.011926540964) / (0.560487912723 * 111.189028235703))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12363]

end BstLean.Part269.N12363

/-! The original eight local profiles supply actual 12363 moment certificates. -/
namespace BstLean.Part269.N12363
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12363 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12363 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12363 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053385707360 ∧
    0 ≤ bN 12363 BstLean.Part154.csC (groupTheta g) ∧ bN 12363 BstLean.Part154.csC (groupTheta g) ≤ 0.001419348643 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12363 12363 0.011
      (momentAllowance 12363 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12363 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12363 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12363 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12363 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12363 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231053472946 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12363 0.011
      (momentAllowance 12363 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12363 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12363
/-! The actual computed-centre upper energy formula at 12363. -/
namespace BstLean.Part269.N12363
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12363

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12363
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12363)
open BstLean.Part268 (cell12363)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086542437463
  | 2 => 0.087506183401
  | 3 => 0.088471392090
  | 4 => 0.089440226207
  | 5 => 0.090415273394
  | 6 => 0.091399605601
  | 7 => 0.092396843322
  | 8 => 0.093411224676
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12363 12363 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12363 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004104440387 + 0.003390347157 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S0.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S0.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12363

/-! Actual upper energy certificates on all 43 source endpoints at 12363. -/
namespace BstLean.Part269.N12363
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12363)
open BstLean.Part268 (cell12363)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12363 (gMinus 12363) (1 - (cell12363 i).lower) ≤ 1 ∧
    energyUpper 12363 (gMinus 12363) (BstLean.Part211.gPlus 12363)
      (finiteEnergy 12363 12363 0.011) (1 - (cell12363 i).lower) ≤
      (cell12363 i).energy := by
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
      have E := BstLean.Part269.S0.uniformEnergy10 (n := 12363) (by norm_num)
        (q := 1 - (cell12363 ⟨10,by decide⟩).lower)
        (by norm_num [cell12363]) (by norm_num [cell12363])
      exact ⟨E.1,E.2.trans (by norm_num [cell12363])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy11 (n := 12363) (by norm_num)
        (q := 1 - (cell12363 ⟨11,by decide⟩).lower)
        (by norm_num [cell12363]) (by norm_num [cell12363])
      exact ⟨E.1,E.2.trans (by norm_num [cell12363])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy12 (n := 12363) (by norm_num)
        (q := 1 - (cell12363 ⟨12,by decide⟩).lower)
        (by norm_num [cell12363]) (by norm_num [cell12363])
      exact ⟨E.1,E.2.trans (by norm_num [cell12363])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy13 (n := 12363) (by norm_num)
        (q := 1 - (cell12363 ⟨13,by decide⟩).lower)
        (by norm_num [cell12363]) (by norm_num [cell12363])
      exact ⟨E.1,E.2.trans (by norm_num [cell12363])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy14 (n := 12363) (by norm_num)
        (q := 1 - (cell12363 ⟨14,by decide⟩).lower)
        (by norm_num [cell12363]) (by norm_num [cell12363])
      exact ⟨E.1,E.2.trans (by norm_num [cell12363])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy15 (n := 12363) (by norm_num)
        (q := 1 - (cell12363 ⟨15,by decide⟩).lower)
        (by norm_num [cell12363]) (by norm_num [cell12363])
      exact ⟨E.1,E.2.trans (by norm_num [cell12363])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy16 (n := 12363) (by norm_num)
        (q := 1 - (cell12363 ⟨16,by decide⟩).lower)
        (by norm_num [cell12363]) (by norm_num [cell12363])
      exact ⟨E.1,E.2.trans (by norm_num [cell12363])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy17 (n := 12363) (by norm_num)
        (q := 1 - (cell12363 ⟨17,by decide⟩).lower)
        (by norm_num [cell12363]) (by norm_num [cell12363])
      exact ⟨E.1,E.2.trans (by norm_num [cell12363])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy18 (n := 12363) (by norm_num)
        (q := 1 - (cell12363 ⟨18,by decide⟩).lower)
        (by norm_num [cell12363]) (by norm_num [cell12363])
      exact ⟨E.1,E.2.trans (by norm_num [cell12363])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy19 (n := 12363) (by norm_num)
        (q := 1 - (cell12363 ⟨19,by decide⟩).lower)
        (by norm_num [cell12363]) (by norm_num [cell12363])
      exact ⟨E.1,E.2.trans (by norm_num [cell12363])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy20 (n := 12363) (by norm_num)
        (q := 1 - (cell12363 ⟨20,by decide⟩).lower)
        (by norm_num [cell12363]) (by norm_num [cell12363])
      exact ⟨E.1,E.2.trans (by norm_num [cell12363])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy21 (n := 12363) (by norm_num)
        (q := 1 - (cell12363 ⟨21,by decide⟩).lower)
        (by norm_num [cell12363]) (by norm_num [cell12363])
      exact ⟨E.1,E.2.trans (by norm_num [cell12363])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy22 (n := 12363) (by norm_num)
        (q := 1 - (cell12363 ⟨22,by decide⟩).lower)
        (by norm_num [cell12363]) (by norm_num [cell12363])
      exact ⟨E.1,E.2.trans (by norm_num [cell12363])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy23 (n := 12363) (by norm_num)
        (q := 1 - (cell12363 ⟨23,by decide⟩).lower)
        (by norm_num [cell12363]) (by norm_num [cell12363])
      exact ⟨E.1,E.2.trans (by norm_num [cell12363])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy24 (n := 12363) (by norm_num)
        (q := 1 - (cell12363 ⟨24,by decide⟩).lower)
        (by norm_num [cell12363]) (by norm_num [cell12363])
      exact ⟨E.1,E.2.trans (by norm_num [cell12363])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy25 (n := 12363) (by norm_num)
        (q := 1 - (cell12363 ⟨25,by decide⟩).lower)
        (by norm_num [cell12363]) (by norm_num [cell12363])
      exact ⟨E.1,E.2.trans (by norm_num [cell12363])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy26 (n := 12363) (by norm_num)
        (q := 1 - (cell12363 ⟨26,by decide⟩).lower)
        (by norm_num [cell12363]) (by norm_num [cell12363])
      exact ⟨E.1,E.2.trans (by norm_num [cell12363])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy27 (n := 12363) (by norm_num)
        (q := 1 - (cell12363 ⟨27,by decide⟩).lower)
        (by norm_num [cell12363]) (by norm_num [cell12363])
      exact ⟨E.1,E.2.trans (by norm_num [cell12363])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy28 (n := 12363) (by norm_num)
        (q := 1 - (cell12363 ⟨28,by decide⟩).lower)
        (by norm_num [cell12363]) (by norm_num [cell12363])
      exact ⟨E.1,E.2.trans (by norm_num [cell12363])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy29 (n := 12363) (by norm_num)
        (q := 1 - (cell12363 ⟨29,by decide⟩).lower)
        (by norm_num [cell12363]) (by norm_num [cell12363])
      exact ⟨E.1,E.2.trans (by norm_num [cell12363])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy30 (n := 12363) (by norm_num)
        (q := 1 - (cell12363 ⟨30,by decide⟩).lower)
        (by norm_num [cell12363]) (by norm_num [cell12363])
      exact ⟨E.1,E.2.trans (by norm_num [cell12363])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy31 (n := 12363) (by norm_num)
        (q := 1 - (cell12363 ⟨31,by decide⟩).lower)
        (by norm_num [cell12363]) (by norm_num [cell12363])
      exact ⟨E.1,E.2.trans (by norm_num [cell12363])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy32 (n := 12363) (by norm_num)
        (q := 1 - (cell12363 ⟨32,by decide⟩).lower)
        (by norm_num [cell12363]) (by norm_num [cell12363])
      exact ⟨E.1,E.2.trans (by norm_num [cell12363])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy33 (n := 12363) (by norm_num)
        (q := 1 - (cell12363 ⟨33,by decide⟩).lower)
        (by norm_num [cell12363]) (by norm_num [cell12363])
      exact ⟨E.1,E.2.trans (by norm_num [cell12363])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy34 (n := 12363) (by norm_num)
        (q := 1 - (cell12363 ⟨34,by decide⟩).lower)
        (by norm_num [cell12363]) (by norm_num [cell12363])
      exact ⟨E.1,E.2.trans (by norm_num [cell12363])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy35 (n := 12363) (by norm_num)
        (q := 1 - (cell12363 ⟨35,by decide⟩).lower)
        (by norm_num [cell12363]) (by norm_num [cell12363])
      exact ⟨E.1,E.2.trans (by norm_num [cell12363])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy36 (n := 12363) (by norm_num)
        (q := 1 - (cell12363 ⟨36,by decide⟩).lower)
        (by norm_num [cell12363]) (by norm_num [cell12363])
      exact ⟨E.1,E.2.trans (by norm_num [cell12363])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy37 (n := 12363) (by norm_num)
        (q := 1 - (cell12363 ⟨37,by decide⟩).lower)
        (by norm_num [cell12363]) (by norm_num [cell12363])
      exact ⟨E.1,E.2.trans (by norm_num [cell12363])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy38 (n := 12363) (by norm_num)
        (q := 1 - (cell12363 ⟨38,by decide⟩).lower)
        (by norm_num [cell12363]) (by norm_num [cell12363])
      exact ⟨E.1,E.2.trans (by norm_num [cell12363])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy39 (n := 12363) (by norm_num)
        (q := 1 - (cell12363 ⟨39,by decide⟩).lower)
        (by norm_num [cell12363]) (by norm_num [cell12363])
      exact ⟨E.1,E.2.trans (by norm_num [cell12363])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy40 (n := 12363) (by norm_num)
        (q := 1 - (cell12363 ⟨40,by decide⟩).lower)
        (by norm_num [cell12363]) (by norm_num [cell12363])
      exact ⟨E.1,E.2.trans (by norm_num [cell12363])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy41 (n := 12363) (by norm_num)
        (q := 1 - (cell12363 ⟨41,by decide⟩).lower)
        (by norm_num [cell12363]) (by norm_num [cell12363])
      exact ⟨E.1,E.2.trans (by norm_num [cell12363])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy42 (n := 12363) (by norm_num)
        (q := 1 - (cell12363 ⟨42,by decide⟩).lower)
        (by norm_num [cell12363]) (by norm_num [cell12363])
      exact ⟨E.1,E.2.trans (by norm_num [cell12363])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy43 (n := 12363) (by norm_num)
        (q := 1 - (cell12363 ⟨43,by decide⟩).lower)
        (by norm_num [cell12363]) (by norm_num [cell12363])
      exact ⟨E.1,E.2.trans (by norm_num [cell12363])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy44 (n := 12363) (by norm_num)
        (q := 1 - (cell12363 ⟨44,by decide⟩).lower)
        (by norm_num [cell12363]) (by norm_num [cell12363])
      exact ⟨E.1,E.2.trans (by norm_num [cell12363])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy45 (n := 12363) (by norm_num)
        (q := 1 - (cell12363 ⟨45,by decide⟩).lower)
        (by norm_num [cell12363]) (by norm_num [cell12363])
      exact ⟨E.1,E.2.trans (by norm_num [cell12363])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy46 (n := 12363) (by norm_num)
        (q := 1 - (cell12363 ⟨46,by decide⟩).lower)
        (by norm_num [cell12363]) (by norm_num [cell12363])
      exact ⟨E.1,E.2.trans (by norm_num [cell12363])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy47 (n := 12363) (by norm_num)
        (q := 1 - (cell12363 ⟨47,by decide⟩).lower)
        (by norm_num [cell12363]) (by norm_num [cell12363])
      exact ⟨E.1,E.2.trans (by norm_num [cell12363])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy48 (n := 12363) (by norm_num)
        (q := 1 - (cell12363 ⟨48,by decide⟩).lower)
        (by norm_num [cell12363]) (by norm_num [cell12363])
      exact ⟨E.1,E.2.trans (by norm_num [cell12363])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy49 (n := 12363) (by norm_num)
        (q := 1 - (cell12363 ⟨49,by decide⟩).lower)
        (by norm_num [cell12363]) (by norm_num [cell12363])
      exact ⟨E.1,E.2.trans (by norm_num [cell12363])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy50 (n := 12363) (by norm_num)
        (q := 1 - (cell12363 ⟨50,by decide⟩).lower)
        (by norm_num [cell12363]) (by norm_num [cell12363])
      exact ⟨E.1,E.2.trans (by norm_num [cell12363])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy51 (n := 12363) (by norm_num)
        (q := 1 - (cell12363 ⟨51,by decide⟩).lower)
        (by norm_num [cell12363]) (by norm_num [cell12363])
      exact ⟨E.1,E.2.trans (by norm_num [cell12363])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy52 (n := 12363) (by norm_num)
        (q := 1 - (cell12363 ⟨52,by decide⟩).lower)
        (by norm_num [cell12363]) (by norm_num [cell12363])
      exact ⟨E.1,E.2.trans (by norm_num [cell12363])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12363

/-! Source-cell containment and simple scalar guards at 12363. -/
namespace BstLean.Part269.N12363
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12363)
open BstLean.Part268 (cell12363)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12363 ⟨10,by decide⟩).lower ∧ (cell12363 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12363 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12363 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12363 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12363 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12363 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12363,cell12363,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12363 ⟨11,by decide⟩).lower ∧ (cell12363 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12363 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12363 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12363 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12363 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12363 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12363,cell12363,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12363 ⟨12,by decide⟩).lower ∧ (cell12363 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12363 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12363 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12363 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12363 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12363 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12363,cell12363,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12363 ⟨13,by decide⟩).lower ∧ (cell12363 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12363 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12363 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12363 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12363 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12363 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12363,cell12363,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12363 ⟨14,by decide⟩).lower ∧ (cell12363 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12363 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12363 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12363 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12363 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12363 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12363,cell12363,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12363 ⟨15,by decide⟩).lower ∧ (cell12363 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12363 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12363 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12363 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12363 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12363 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12363,cell12363,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12363 ⟨16,by decide⟩).lower ∧ (cell12363 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12363 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12363 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12363 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12363 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12363 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12363,cell12363,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12363 ⟨17,by decide⟩).lower ∧ (cell12363 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12363 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12363 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12363 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12363 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12363 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12363,cell12363,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12363 ⟨18,by decide⟩).lower ∧ (cell12363 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12363 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12363 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12363 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12363 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12363 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12363,cell12363,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12363 ⟨19,by decide⟩).lower ∧ (cell12363 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12363 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12363 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12363 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12363 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12363 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12363,cell12363,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12363 ⟨20,by decide⟩).lower ∧ (cell12363 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12363 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12363 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12363 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12363 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12363 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12363,cell12363,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12363 ⟨21,by decide⟩).lower ∧ (cell12363 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12363 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12363 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12363 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12363 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12363 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12363,cell12363,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12363 ⟨22,by decide⟩).lower ∧ (cell12363 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12363 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12363 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12363 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12363 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12363 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12363,cell12363,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12363 ⟨23,by decide⟩).lower ∧ (cell12363 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12363 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12363 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12363 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12363 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12363 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12363,cell12363,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12363 ⟨24,by decide⟩).lower ∧ (cell12363 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12363 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12363 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12363 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12363 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12363 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12363,cell12363,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12363 ⟨25,by decide⟩).lower ∧ (cell12363 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12363 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12363 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12363 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12363 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12363 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12363,cell12363,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12363 ⟨26,by decide⟩).lower ∧ (cell12363 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12363 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12363 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12363 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12363 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12363 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12363,cell12363,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12363 ⟨27,by decide⟩).lower ∧ (cell12363 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12363 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12363 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12363 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12363 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12363 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12363,cell12363,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12363 ⟨28,by decide⟩).lower ∧ (cell12363 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12363 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12363 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12363 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12363 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12363 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12363,cell12363,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12363 ⟨29,by decide⟩).lower ∧ (cell12363 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12363 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12363 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12363 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12363 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12363 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12363,cell12363,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12363 ⟨30,by decide⟩).lower ∧ (cell12363 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12363 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12363 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12363 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12363 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12363 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12363,cell12363,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12363 ⟨31,by decide⟩).lower ∧ (cell12363 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12363 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12363 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12363 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12363 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12363 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12363,cell12363,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12363 ⟨32,by decide⟩).lower ∧ (cell12363 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12363 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12363 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12363 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12363 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12363 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12363,cell12363,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12363 ⟨33,by decide⟩).lower ∧ (cell12363 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12363 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12363 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12363 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12363 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12363 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12363,cell12363,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12363 ⟨34,by decide⟩).lower ∧ (cell12363 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12363 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12363 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12363 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12363 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12363 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12363,cell12363,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12363 ⟨35,by decide⟩).lower ∧ (cell12363 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12363 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12363 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12363 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12363 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12363 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12363,cell12363,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12363 ⟨36,by decide⟩).lower ∧ (cell12363 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12363 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12363 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12363 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12363 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12363 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12363,cell12363,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12363 ⟨37,by decide⟩).lower ∧ (cell12363 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12363 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12363 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12363 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12363 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12363 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12363,cell12363,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12363 ⟨38,by decide⟩).lower ∧ (cell12363 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12363 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12363 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12363 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12363 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12363 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12363,cell12363,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12363 ⟨39,by decide⟩).lower ∧ (cell12363 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12363 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12363 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12363 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12363 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12363 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12363,cell12363,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12363 ⟨40,by decide⟩).lower ∧ (cell12363 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12363 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12363 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12363 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12363 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12363 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12363,cell12363,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12363 ⟨41,by decide⟩).lower ∧ (cell12363 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12363 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12363 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12363 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12363 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12363 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12363,cell12363,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12363 ⟨42,by decide⟩).lower ∧ (cell12363 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12363 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12363 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12363 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12363 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12363 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12363,cell12363,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12363 ⟨43,by decide⟩).lower ∧ (cell12363 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12363 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12363 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12363 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12363 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12363 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12363,cell12363,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12363 ⟨44,by decide⟩).lower ∧ (cell12363 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12363 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12363 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12363 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12363 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12363 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12363,cell12363,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12363 ⟨45,by decide⟩).lower ∧ (cell12363 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12363 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12363 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12363 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12363 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12363 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12363,cell12363,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12363 ⟨46,by decide⟩).lower ∧ (cell12363 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12363 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12363 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12363 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12363 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12363 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12363,cell12363,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12363 ⟨47,by decide⟩).lower ∧ (cell12363 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12363 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12363 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12363 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12363 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12363 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12363,cell12363,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12363 ⟨48,by decide⟩).lower ∧ (cell12363 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12363 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12363 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12363 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12363 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12363 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12363,cell12363,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12363 ⟨49,by decide⟩).lower ∧ (cell12363 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12363 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12363 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12363 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12363 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12363 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12363,cell12363,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12363 ⟨50,by decide⟩).lower ∧ (cell12363 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12363 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12363 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12363 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12363 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12363 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12363,cell12363,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12363 ⟨51,by decide⟩).lower ∧ (cell12363 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12363 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12363 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12363 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12363 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12363 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12363,cell12363,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12363 ⟨52,by decide⟩).lower ∧ (cell12363 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12363 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12363 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12363 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12363 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12363 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12363,cell12363,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12363 i).lower ∧
    (cell12363 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12363 i).upper ≤ (0.532 : ℝ) ∧
    (cell12363 i).centre ≤ (0.1 : ℝ) ∧ (cell12363 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12363 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12363 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12363

/-! The local source numeric instances at 12363 have no network premises. -/
namespace BstLean.Part269.N12363
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12363)
open BstLean.Part268 (cell12363)

noncomputable def sourceNumerics12363 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12363 (cell12363 i)
      scalarRow12363.M scalarRow12363.H scalarRow12363.xi := by
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
    energy_allowance := scalarRow12363.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12363]
    centre_nonneg := (scalarRow12363.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D0.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12363])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12363