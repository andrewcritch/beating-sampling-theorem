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
import BstLean.Part269Direction27
import BstLean.Part269Shared27
import BstLean.Part269Finite
import BstLean.Part269Rows27
import BstLean.Part269Source
/-! Actual 13025 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13025
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13025 ≤ (1.035355738075 : ℝ) := by
  have hr : (114.127122105133 : ℝ) ≤ √(13025 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.127122105133 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13025 13025 (11 / 1000) ≤
    (0.008375633415 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13025) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.127122105133 : ℝ) ≤ √(13025 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13025)
  have hdiv : K / √(13025 : ℝ) ≤ K / 114.127122105133 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.127122105133 ≤ (0.008375633415 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13025.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13025 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13025 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13025 := gPlus_lower 13025
end BstLean.Part269.N13025

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13025
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035355738074 : ℝ) ≤ wn 13025 := by
  have hn : √(13025 : ℝ) ≤ 114.127122105134 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13025 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.127122105134 ≤ 2 / √(13025 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000245488410 : ℝ) ≤ rhoBar 13025 BstLean.Part154.csC ∧
    rhoBar 13025 BstLean.Part154.csC ≤ 0.000245488790 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035355738074 : ℝ) / (1.295212 * 13025) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035355738075 : ℝ) / (1.29521 * 13025) := by gcongr
      _ ≤ (0.000245488790 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13025 BstLean.Part154.csC) ≤ 0.000982015425 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13025 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13025 BstLean.Part154.csC) (piBar (rhoBar 13025 BstLean.Part154.csC)) ≤ 0.000187505773 ∧
    cc1 (rhoBar 13025 BstLean.Part154.csC) (piBar (rhoBar 13025 BstLean.Part154.csC)) ≤ 0.000119311214 ∧
    cc2 (rhoBar 13025 BstLean.Part154.csC) ≤ 0.000069261129 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13025 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13025 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13025 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13025 BstLean.Part154.csC * nuR (rhoBar 13025 BstLean.Part154.csC)) ≤ 0.000490992647 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000245488790 : ℝ) * 0.000982015425 := by gcongr
      _ ≤ (0.000490992647 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13025 BstLean.Part154.csC) * nuR (rhoBar 13025 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000982015425 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13025 BstLean.Part154.csC) * rhoBar 13025 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000245488790 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000245488790 / 2 + 0.399 * 0.000982015425 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000187505773 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000490992647 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119311214 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000245488790 / 1.414213562 := by gcongr
      _ ≤ (0.000069261129 : ℝ) := by norm_num

end BstLean.Part269.N13025

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13025
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13025 BstLean.Part154.csC) (piBar (rhoBar 13025 BstLean.Part154.csC)) ≤ 1.51833E-7 := by
  have hr0 : 0 ≤ rhoBar 13025 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13025 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13025 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13025 BstLean.Part154.csC) (piBar (rhoBar 13025 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13025 BstLean.Part154.csC) (piBar (rhoBar 13025 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13025 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000187505773 : ℝ) ^ 2 + 0.000119311214 ^ 2 + 3 * 0.000069261129 ^ 2 +
        2 * 0.797885 * 0.000187505773 * 0.000119311214 + 2 * 0.000187505773 * 0.000069261129 +
        4 * 0.797885 * 0.000119311214 * 0.000069261129 := by gcongr
    _ ≤ (1.51833E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13025 BstLean.Part154.csC Θ ≤ 0.002561443415 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13025 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13025 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13025 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13025 BstLean.Part154.csC) (piBar (rhoBar 13025 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13025 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035355738075 * 1.51833E-7 / (0.000245488410 : ℝ) := by gcongr
    _ ≤ 0.002561443415 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13025 BstLean.Part154.csC Θ ≤ 0.002840805561 + 0.000647234211 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13025 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13025 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13025 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035355738075 : ℝ) * ((2 * Θ * 0.000245488790 +
        (6863 / 10000) * 0.000245488790 * 13025 * 0.000982015425) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002840805561 + 0.000647234211 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13025 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13025 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13025 0.011 Θ ∧ gammaRatio 13025 0.011 Θ ≤ 0.000084392698 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13025 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035355738075 : ℝ) * 0.525 / ((1 - 0.011) * 13025) := by gcongr
      _ ≤ (0.000084392698 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13025 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13025 0.011 Θ) :=
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
    badAllowance 13025 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000383431726 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13025 BstLean.Part154.csC) 1.22 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 2 (rhoBar 13025 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13025 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13025 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13025 0.011 Θ) 1.12 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 1 (gammaRatio 13025 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13025 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13025 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13025 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13025 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035355738075 : ℝ) * 13025 *
        (1.3781E-8 / 1.1045361 + 1.6832E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000383431726 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13025 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003224237287 + 0.003208677626 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13025

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13025
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13025 BstLean.Part154.csC) (piBar (rhoBar 13025 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13025 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13025 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13025 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13025 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13025 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13025 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13025 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13025 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13025 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13025 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13025 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13025 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13025 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13025 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051818326336 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13025) ≤ 0.010464099673 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13025 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035355738075)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010464099673 + 2 * 0.737676 / 13025) := by gcongr
    _ ≤ (0.051818326336 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13025 12 ≤ 0.0015 := by
  exact BstLean.Part269.S27.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13025

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13025
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560517899024 : ℝ) ≤ plow 13025 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13025) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052415393041)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001344757793) : eMP 13025 0.011 xi bn ≤ 0.001158137698 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13025 : ℝ) * (1 - 0.011))) ≤ 0.000572677320 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001344757793 / (13025 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000572677320 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000572677320 : ℝ) + 3.141593 * 0.052415393041 / (13025 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001158137698 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052415393041)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001344757793) : PiBarMP 13025 12 0.011 xi bn ≤ 0.159206519262 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13025 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036670939353 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.497687201105 : ℝ) ≤ √((13025 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.127122105133 : ℝ) ≤ √(13025 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13025) ≤ 0.122077977661 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036670939353 + 0.052415393041 * 1.772454 / (2 * (113.497687201105 : ℝ))) * (1 + 0.001158137698) +
        8 / (13025 * 114.127122105133) + 0.122077977661 := by gcongr
    _ ≤ (0.159206519262 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052415393041)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001344757793) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280762409119) :
    parallelOracle 13025 0.011 xi bn cd ≤ 0.160172020022 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13025 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13025 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560517899024 : ℝ) ≤ plow 13025 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.127122105133 : ℝ) ≤ √(13025 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280762409119 : ℝ) / (2 * 0.560517899024 * 114.127122105133)) * 0.159206519262 +
        0.280762409119 ^ 2 / (2 * 0.560517899024 * 114.127122105133) := by gcongr
    _ ≤ (0.160172020022 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052415393041) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001344757793)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280762409119) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13025 13025 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560517899024 : ℝ) ≤ plow 13025 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.127122105133 : ℝ) ≤ √(13025 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13025 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13025 Θ 1.22 ≤ 0.011619503547 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.127122105133 := by gcongr <;> linarith
      _ ≤ (0.011619503547 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13025 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13025 13025 0.011 ≤ 0.008375633415 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13025 13025 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13025 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13025 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13025 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13025 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160172020022 + 0.011619503547 + (0.008375633415 : ℝ) *
        (1 + 2 * (0.280762409119 + 0.011619503547) / (0.560517899024 * 114.127122105133))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13025]

end BstLean.Part269.N13025

/-! The original eight local profiles supply actual 13025 moment certificates. -/
namespace BstLean.Part269.N13025
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13025 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13025 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13025 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052415393041 ∧
    0 ≤ bN 13025 BstLean.Part154.csC (groupTheta g) ∧ bN 13025 BstLean.Part154.csC (groupTheta g) ≤ 0.001344757793 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13025 13025 0.011
      (momentAllowance 13025 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13025 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13025 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13025 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13025 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13025 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228944082783 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13025 0.011
      (momentAllowance 13025 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13025 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13025
/-! The actual computed-centre upper energy formula at 13025. -/
namespace BstLean.Part269.N13025
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13025

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13025
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13025)
open BstLean.Part268 (cell13025)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084594899912
  | 2 => 0.085522718013
  | 3 => 0.086446615778
  | 4 => 0.087367527217
  | 5 => 0.088286596220
  | 6 => 0.089205209483
  | 7 => 0.090125032869
  | 8 => 0.091048051290
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13025 13025 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13025 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003224237287 + 0.003208677626 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S27.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13025

/-! Actual upper energy certificates on all 43 source endpoints at 13025. -/
namespace BstLean.Part269.N13025
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13025)
open BstLean.Part268 (cell13025)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13025 (gMinus 13025) (1 - (cell13025 i).lower) ≤ 1 ∧
    energyUpper 13025 (gMinus 13025) (BstLean.Part211.gPlus 13025)
      (finiteEnergy 13025 13025 0.011) (1 - (cell13025 i).lower) ≤
      (cell13025 i).energy := by
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
      have E := BstLean.Part269.S27.uniformEnergy10 (n := 13025) (by norm_num)
        (q := 1 - (cell13025 ⟨10,by decide⟩).lower)
        (by norm_num [cell13025]) (by norm_num [cell13025])
      exact ⟨E.1,E.2.trans (by norm_num [cell13025])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy11 (n := 13025) (by norm_num)
        (q := 1 - (cell13025 ⟨11,by decide⟩).lower)
        (by norm_num [cell13025]) (by norm_num [cell13025])
      exact ⟨E.1,E.2.trans (by norm_num [cell13025])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy12 (n := 13025) (by norm_num)
        (q := 1 - (cell13025 ⟨12,by decide⟩).lower)
        (by norm_num [cell13025]) (by norm_num [cell13025])
      exact ⟨E.1,E.2.trans (by norm_num [cell13025])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy13 (n := 13025) (by norm_num)
        (q := 1 - (cell13025 ⟨13,by decide⟩).lower)
        (by norm_num [cell13025]) (by norm_num [cell13025])
      exact ⟨E.1,E.2.trans (by norm_num [cell13025])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy14 (n := 13025) (by norm_num)
        (q := 1 - (cell13025 ⟨14,by decide⟩).lower)
        (by norm_num [cell13025]) (by norm_num [cell13025])
      exact ⟨E.1,E.2.trans (by norm_num [cell13025])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy15 (n := 13025) (by norm_num)
        (q := 1 - (cell13025 ⟨15,by decide⟩).lower)
        (by norm_num [cell13025]) (by norm_num [cell13025])
      exact ⟨E.1,E.2.trans (by norm_num [cell13025])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy16 (n := 13025) (by norm_num)
        (q := 1 - (cell13025 ⟨16,by decide⟩).lower)
        (by norm_num [cell13025]) (by norm_num [cell13025])
      exact ⟨E.1,E.2.trans (by norm_num [cell13025])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy17 (n := 13025) (by norm_num)
        (q := 1 - (cell13025 ⟨17,by decide⟩).lower)
        (by norm_num [cell13025]) (by norm_num [cell13025])
      exact ⟨E.1,E.2.trans (by norm_num [cell13025])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy18 (n := 13025) (by norm_num)
        (q := 1 - (cell13025 ⟨18,by decide⟩).lower)
        (by norm_num [cell13025]) (by norm_num [cell13025])
      exact ⟨E.1,E.2.trans (by norm_num [cell13025])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy19 (n := 13025) (by norm_num)
        (q := 1 - (cell13025 ⟨19,by decide⟩).lower)
        (by norm_num [cell13025]) (by norm_num [cell13025])
      exact ⟨E.1,E.2.trans (by norm_num [cell13025])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy20 (n := 13025) (by norm_num)
        (q := 1 - (cell13025 ⟨20,by decide⟩).lower)
        (by norm_num [cell13025]) (by norm_num [cell13025])
      exact ⟨E.1,E.2.trans (by norm_num [cell13025])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy21 (n := 13025) (by norm_num)
        (q := 1 - (cell13025 ⟨21,by decide⟩).lower)
        (by norm_num [cell13025]) (by norm_num [cell13025])
      exact ⟨E.1,E.2.trans (by norm_num [cell13025])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy22 (n := 13025) (by norm_num)
        (q := 1 - (cell13025 ⟨22,by decide⟩).lower)
        (by norm_num [cell13025]) (by norm_num [cell13025])
      exact ⟨E.1,E.2.trans (by norm_num [cell13025])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy23 (n := 13025) (by norm_num)
        (q := 1 - (cell13025 ⟨23,by decide⟩).lower)
        (by norm_num [cell13025]) (by norm_num [cell13025])
      exact ⟨E.1,E.2.trans (by norm_num [cell13025])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy24 (n := 13025) (by norm_num)
        (q := 1 - (cell13025 ⟨24,by decide⟩).lower)
        (by norm_num [cell13025]) (by norm_num [cell13025])
      exact ⟨E.1,E.2.trans (by norm_num [cell13025])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy25 (n := 13025) (by norm_num)
        (q := 1 - (cell13025 ⟨25,by decide⟩).lower)
        (by norm_num [cell13025]) (by norm_num [cell13025])
      exact ⟨E.1,E.2.trans (by norm_num [cell13025])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy26 (n := 13025) (by norm_num)
        (q := 1 - (cell13025 ⟨26,by decide⟩).lower)
        (by norm_num [cell13025]) (by norm_num [cell13025])
      exact ⟨E.1,E.2.trans (by norm_num [cell13025])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy27 (n := 13025) (by norm_num)
        (q := 1 - (cell13025 ⟨27,by decide⟩).lower)
        (by norm_num [cell13025]) (by norm_num [cell13025])
      exact ⟨E.1,E.2.trans (by norm_num [cell13025])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy28 (n := 13025) (by norm_num)
        (q := 1 - (cell13025 ⟨28,by decide⟩).lower)
        (by norm_num [cell13025]) (by norm_num [cell13025])
      exact ⟨E.1,E.2.trans (by norm_num [cell13025])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy29 (n := 13025) (by norm_num)
        (q := 1 - (cell13025 ⟨29,by decide⟩).lower)
        (by norm_num [cell13025]) (by norm_num [cell13025])
      exact ⟨E.1,E.2.trans (by norm_num [cell13025])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy30 (n := 13025) (by norm_num)
        (q := 1 - (cell13025 ⟨30,by decide⟩).lower)
        (by norm_num [cell13025]) (by norm_num [cell13025])
      exact ⟨E.1,E.2.trans (by norm_num [cell13025])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy31 (n := 13025) (by norm_num)
        (q := 1 - (cell13025 ⟨31,by decide⟩).lower)
        (by norm_num [cell13025]) (by norm_num [cell13025])
      exact ⟨E.1,E.2.trans (by norm_num [cell13025])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy32 (n := 13025) (by norm_num)
        (q := 1 - (cell13025 ⟨32,by decide⟩).lower)
        (by norm_num [cell13025]) (by norm_num [cell13025])
      exact ⟨E.1,E.2.trans (by norm_num [cell13025])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy33 (n := 13025) (by norm_num)
        (q := 1 - (cell13025 ⟨33,by decide⟩).lower)
        (by norm_num [cell13025]) (by norm_num [cell13025])
      exact ⟨E.1,E.2.trans (by norm_num [cell13025])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy34 (n := 13025) (by norm_num)
        (q := 1 - (cell13025 ⟨34,by decide⟩).lower)
        (by norm_num [cell13025]) (by norm_num [cell13025])
      exact ⟨E.1,E.2.trans (by norm_num [cell13025])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy35 (n := 13025) (by norm_num)
        (q := 1 - (cell13025 ⟨35,by decide⟩).lower)
        (by norm_num [cell13025]) (by norm_num [cell13025])
      exact ⟨E.1,E.2.trans (by norm_num [cell13025])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy36 (n := 13025) (by norm_num)
        (q := 1 - (cell13025 ⟨36,by decide⟩).lower)
        (by norm_num [cell13025]) (by norm_num [cell13025])
      exact ⟨E.1,E.2.trans (by norm_num [cell13025])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy37 (n := 13025) (by norm_num)
        (q := 1 - (cell13025 ⟨37,by decide⟩).lower)
        (by norm_num [cell13025]) (by norm_num [cell13025])
      exact ⟨E.1,E.2.trans (by norm_num [cell13025])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy38 (n := 13025) (by norm_num)
        (q := 1 - (cell13025 ⟨38,by decide⟩).lower)
        (by norm_num [cell13025]) (by norm_num [cell13025])
      exact ⟨E.1,E.2.trans (by norm_num [cell13025])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy39 (n := 13025) (by norm_num)
        (q := 1 - (cell13025 ⟨39,by decide⟩).lower)
        (by norm_num [cell13025]) (by norm_num [cell13025])
      exact ⟨E.1,E.2.trans (by norm_num [cell13025])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy40 (n := 13025) (by norm_num)
        (q := 1 - (cell13025 ⟨40,by decide⟩).lower)
        (by norm_num [cell13025]) (by norm_num [cell13025])
      exact ⟨E.1,E.2.trans (by norm_num [cell13025])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy41 (n := 13025) (by norm_num)
        (q := 1 - (cell13025 ⟨41,by decide⟩).lower)
        (by norm_num [cell13025]) (by norm_num [cell13025])
      exact ⟨E.1,E.2.trans (by norm_num [cell13025])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy42 (n := 13025) (by norm_num)
        (q := 1 - (cell13025 ⟨42,by decide⟩).lower)
        (by norm_num [cell13025]) (by norm_num [cell13025])
      exact ⟨E.1,E.2.trans (by norm_num [cell13025])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy43 (n := 13025) (by norm_num)
        (q := 1 - (cell13025 ⟨43,by decide⟩).lower)
        (by norm_num [cell13025]) (by norm_num [cell13025])
      exact ⟨E.1,E.2.trans (by norm_num [cell13025])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy44 (n := 13025) (by norm_num)
        (q := 1 - (cell13025 ⟨44,by decide⟩).lower)
        (by norm_num [cell13025]) (by norm_num [cell13025])
      exact ⟨E.1,E.2.trans (by norm_num [cell13025])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy45 (n := 13025) (by norm_num)
        (q := 1 - (cell13025 ⟨45,by decide⟩).lower)
        (by norm_num [cell13025]) (by norm_num [cell13025])
      exact ⟨E.1,E.2.trans (by norm_num [cell13025])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy46 (n := 13025) (by norm_num)
        (q := 1 - (cell13025 ⟨46,by decide⟩).lower)
        (by norm_num [cell13025]) (by norm_num [cell13025])
      exact ⟨E.1,E.2.trans (by norm_num [cell13025])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy47 (n := 13025) (by norm_num)
        (q := 1 - (cell13025 ⟨47,by decide⟩).lower)
        (by norm_num [cell13025]) (by norm_num [cell13025])
      exact ⟨E.1,E.2.trans (by norm_num [cell13025])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy48 (n := 13025) (by norm_num)
        (q := 1 - (cell13025 ⟨48,by decide⟩).lower)
        (by norm_num [cell13025]) (by norm_num [cell13025])
      exact ⟨E.1,E.2.trans (by norm_num [cell13025])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy49 (n := 13025) (by norm_num)
        (q := 1 - (cell13025 ⟨49,by decide⟩).lower)
        (by norm_num [cell13025]) (by norm_num [cell13025])
      exact ⟨E.1,E.2.trans (by norm_num [cell13025])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy50 (n := 13025) (by norm_num)
        (q := 1 - (cell13025 ⟨50,by decide⟩).lower)
        (by norm_num [cell13025]) (by norm_num [cell13025])
      exact ⟨E.1,E.2.trans (by norm_num [cell13025])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy51 (n := 13025) (by norm_num)
        (q := 1 - (cell13025 ⟨51,by decide⟩).lower)
        (by norm_num [cell13025]) (by norm_num [cell13025])
      exact ⟨E.1,E.2.trans (by norm_num [cell13025])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy52 (n := 13025) (by norm_num)
        (q := 1 - (cell13025 ⟨52,by decide⟩).lower)
        (by norm_num [cell13025]) (by norm_num [cell13025])
      exact ⟨E.1,E.2.trans (by norm_num [cell13025])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13025

/-! Source-cell containment and simple scalar guards at 13025. -/
namespace BstLean.Part269.N13025
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13025)
open BstLean.Part268 (cell13025)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13025 ⟨10,by decide⟩).lower ∧ (cell13025 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13025 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13025 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13025 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13025 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13025 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13025,cell13025,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13025 ⟨11,by decide⟩).lower ∧ (cell13025 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13025 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13025 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13025 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13025 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13025 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13025,cell13025,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13025 ⟨12,by decide⟩).lower ∧ (cell13025 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13025 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13025 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13025 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13025 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13025 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13025,cell13025,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13025 ⟨13,by decide⟩).lower ∧ (cell13025 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13025 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13025 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13025 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13025 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13025 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13025,cell13025,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13025 ⟨14,by decide⟩).lower ∧ (cell13025 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13025 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13025 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13025 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13025 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13025 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13025,cell13025,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13025 ⟨15,by decide⟩).lower ∧ (cell13025 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13025 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13025 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13025 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13025 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13025 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13025,cell13025,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13025 ⟨16,by decide⟩).lower ∧ (cell13025 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13025 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13025 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13025 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13025 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13025 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13025,cell13025,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13025 ⟨17,by decide⟩).lower ∧ (cell13025 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13025 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13025 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13025 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13025 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13025 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13025,cell13025,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13025 ⟨18,by decide⟩).lower ∧ (cell13025 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13025 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13025 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13025 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13025 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13025 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13025,cell13025,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13025 ⟨19,by decide⟩).lower ∧ (cell13025 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13025 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13025 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13025 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13025 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13025 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13025,cell13025,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13025 ⟨20,by decide⟩).lower ∧ (cell13025 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13025 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13025 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13025 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13025 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13025 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13025,cell13025,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13025 ⟨21,by decide⟩).lower ∧ (cell13025 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13025 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13025 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13025 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13025 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13025 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13025,cell13025,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13025 ⟨22,by decide⟩).lower ∧ (cell13025 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13025 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13025 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13025 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13025 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13025 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13025,cell13025,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13025 ⟨23,by decide⟩).lower ∧ (cell13025 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13025 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13025 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13025 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13025 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13025 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13025,cell13025,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13025 ⟨24,by decide⟩).lower ∧ (cell13025 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13025 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13025 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13025 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13025 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13025 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13025,cell13025,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13025 ⟨25,by decide⟩).lower ∧ (cell13025 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13025 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13025 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13025 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13025 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13025 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13025,cell13025,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13025 ⟨26,by decide⟩).lower ∧ (cell13025 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13025 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13025 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13025 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13025 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13025 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13025,cell13025,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13025 ⟨27,by decide⟩).lower ∧ (cell13025 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13025 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13025 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13025 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13025 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13025 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13025,cell13025,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13025 ⟨28,by decide⟩).lower ∧ (cell13025 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13025 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13025 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13025 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13025 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13025 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13025,cell13025,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13025 ⟨29,by decide⟩).lower ∧ (cell13025 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13025 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13025 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13025 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13025 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13025 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13025,cell13025,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13025 ⟨30,by decide⟩).lower ∧ (cell13025 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13025 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13025 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13025 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13025 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13025 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13025,cell13025,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13025 ⟨31,by decide⟩).lower ∧ (cell13025 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13025 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13025 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13025 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13025 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13025 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13025,cell13025,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13025 ⟨32,by decide⟩).lower ∧ (cell13025 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13025 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13025 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13025 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13025 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13025 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13025,cell13025,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13025 ⟨33,by decide⟩).lower ∧ (cell13025 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13025 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13025 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13025 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13025 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13025 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13025,cell13025,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13025 ⟨34,by decide⟩).lower ∧ (cell13025 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13025 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13025 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13025 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13025 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13025 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13025,cell13025,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13025 ⟨35,by decide⟩).lower ∧ (cell13025 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13025 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13025 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13025 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13025 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13025 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13025,cell13025,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13025 ⟨36,by decide⟩).lower ∧ (cell13025 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13025 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13025 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13025 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13025 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13025 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13025,cell13025,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13025 ⟨37,by decide⟩).lower ∧ (cell13025 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13025 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13025 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13025 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13025 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13025 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13025,cell13025,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13025 ⟨38,by decide⟩).lower ∧ (cell13025 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13025 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13025 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13025 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13025 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13025 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13025,cell13025,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13025 ⟨39,by decide⟩).lower ∧ (cell13025 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13025 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13025 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13025 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13025 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13025 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13025,cell13025,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13025 ⟨40,by decide⟩).lower ∧ (cell13025 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13025 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13025 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13025 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13025 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13025 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13025,cell13025,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13025 ⟨41,by decide⟩).lower ∧ (cell13025 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13025 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13025 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13025 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13025 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13025 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13025,cell13025,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13025 ⟨42,by decide⟩).lower ∧ (cell13025 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13025 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13025 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13025 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13025 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13025 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13025,cell13025,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13025 ⟨43,by decide⟩).lower ∧ (cell13025 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13025 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13025 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13025 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13025 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13025 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13025,cell13025,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13025 ⟨44,by decide⟩).lower ∧ (cell13025 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13025 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13025 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13025 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13025 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13025 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13025,cell13025,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13025 ⟨45,by decide⟩).lower ∧ (cell13025 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13025 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13025 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13025 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13025 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13025 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13025,cell13025,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13025 ⟨46,by decide⟩).lower ∧ (cell13025 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13025 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13025 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13025 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13025 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13025 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13025,cell13025,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13025 ⟨47,by decide⟩).lower ∧ (cell13025 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13025 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13025 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13025 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13025 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13025 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13025,cell13025,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13025 ⟨48,by decide⟩).lower ∧ (cell13025 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13025 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13025 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13025 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13025 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13025 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13025,cell13025,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13025 ⟨49,by decide⟩).lower ∧ (cell13025 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13025 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13025 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13025 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13025 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13025 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13025,cell13025,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13025 ⟨50,by decide⟩).lower ∧ (cell13025 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13025 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13025 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13025 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13025 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13025 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13025,cell13025,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13025 ⟨51,by decide⟩).lower ∧ (cell13025 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13025 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13025 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13025 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13025 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13025 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13025,cell13025,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13025 ⟨52,by decide⟩).lower ∧ (cell13025 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13025 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13025 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13025 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13025 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13025 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13025,cell13025,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13025 i).lower ∧
    (cell13025 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13025 i).upper ≤ (0.532 : ℝ) ∧
    (cell13025 i).centre ≤ (0.1 : ℝ) ∧ (cell13025 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13025 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13025 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13025

/-! The local source numeric instances at 13025 have no network premises. -/
namespace BstLean.Part269.N13025
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13025)
open BstLean.Part268 (cell13025)

noncomputable def sourceNumerics13025 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13025 (cell13025 i)
      scalarRow13025.M scalarRow13025.H scalarRow13025.xi := by
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
    energy_allowance := scalarRow13025.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13025]
    centre_nonneg := (scalarRow13025.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D27.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13025])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13025
/-! Actual 13026 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13026
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13026 ≤ (1.035354369139 : ℝ) := by
  have hr : (114.131503100590 : ℝ) ≤ √(13026 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.131503100590 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13026 13026 (11 / 1000) ≤
    (0.008375311909 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13026) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.131503100590 : ℝ) ≤ √(13026 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13026)
  have hdiv : K / √(13026 : ℝ) ≤ K / 114.131503100590 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.131503100590 ≤ (0.008375311909 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13026.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13026 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13026 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13026 := gPlus_lower 13026
end BstLean.Part269.N13026

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13026
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035354369138 : ℝ) ≤ wn 13026 := by
  have hn : √(13026 : ℝ) ≤ 114.131503100591 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13026 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.131503100591 ≤ 2 / √(13026 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000245469240 : ℝ) ≤ rhoBar 13026 BstLean.Part154.csC ∧
    rhoBar 13026 BstLean.Part154.csC ≤ 0.000245469620 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035354369138 : ℝ) / (1.295212 * 13026) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035354369139 : ℝ) / (1.29521 * 13026) := by gcongr
      _ ≤ (0.000245469620 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13026 BstLean.Part154.csC) ≤ 0.000981938736 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13026 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13026 BstLean.Part154.csC) (piBar (rhoBar 13026 BstLean.Part154.csC)) ≤ 0.000187491130 ∧
    cc1 (rhoBar 13026 BstLean.Part154.csC) (piBar (rhoBar 13026 BstLean.Part154.csC)) ≤ 0.000119301896 ∧
    cc2 (rhoBar 13026 BstLean.Part154.csC) ≤ 0.000069255720 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13026 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13026 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13026 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13026 BstLean.Part154.csC * nuR (rhoBar 13026 BstLean.Part154.csC)) ≤ 0.000490954304 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000245469620 : ℝ) * 0.000981938736 := by gcongr
      _ ≤ (0.000490954304 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13026 BstLean.Part154.csC) * nuR (rhoBar 13026 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000981938736 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13026 BstLean.Part154.csC) * rhoBar 13026 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000245469620 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000245469620 / 2 + 0.399 * 0.000981938736 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000187491130 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000490954304 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119301896 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000245469620 / 1.414213562 := by gcongr
      _ ≤ (0.000069255720 : ℝ) := by norm_num

end BstLean.Part269.N13026

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13026
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13026 BstLean.Part154.csC) (piBar (rhoBar 13026 BstLean.Part154.csC)) ≤ 1.51809E-7 := by
  have hr0 : 0 ≤ rhoBar 13026 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13026 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13026 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13026 BstLean.Part154.csC) (piBar (rhoBar 13026 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13026 BstLean.Part154.csC) (piBar (rhoBar 13026 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13026 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000187491130 : ℝ) ^ 2 + 0.000119301896 ^ 2 + 3 * 0.000069255720 ^ 2 +
        2 * 0.797885 * 0.000187491130 * 0.000119301896 + 2 * 0.000187491130 * 0.000069255720 +
        4 * 0.797885 * 0.000119301896 * 0.000069255720 := by gcongr
    _ ≤ (1.51809E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13026 BstLean.Part154.csC Θ ≤ 0.002561235150 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13026 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13026 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13026 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13026 BstLean.Part154.csC) (piBar (rhoBar 13026 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13026 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035354369139 * 1.51809E-7 / (0.000245469240 : ℝ) := by gcongr
    _ ≤ 0.002561235150 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13026 BstLean.Part154.csC Θ ≤ 0.002840576208 + 0.000647182814 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13026 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13026 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13026 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035354369139 : ℝ) * ((2 * Θ * 0.000245469620 +
        (6863 / 10000) * 0.000245469620 * 13026 * 0.000981938736) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002840576208 + 0.000647182814 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13026 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13026 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13026 0.011 Θ ∧ gammaRatio 13026 0.011 Θ ≤ 0.000084386108 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13026 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035354369139 : ℝ) * 0.525 / ((1 - 0.011) * 13026) := by gcongr
      _ ≤ (0.000084386108 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13026 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13026 0.011 Θ) :=
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
    badAllowance 13026 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000383431726 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13026 BstLean.Part154.csC) 1.22 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 2 (rhoBar 13026 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13026 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13026 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13026 0.011 Θ) 1.12 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 1 (gammaRatio 13026 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13026 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13026 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13026 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13026 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035354369139 : ℝ) * 13026 *
        (1.3781E-8 / 1.1045361 + 1.6832E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000383431726 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13026 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003224007934 + 0.003208417964 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13026

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13026
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13026 BstLean.Part154.csC) (piBar (rhoBar 13026 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13026 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13026 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13026 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13026 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13026 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13026 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13026 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13026 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13026 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13026 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13026 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13026 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13026 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13026 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051816315963 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13026) ≤ 0.010463698003 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13026 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035354369139)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010463698003 + 2 * 0.737676 / 13026) := by gcongr
    _ ≤ (0.051816315963 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13026 12 ≤ 0.0015 := by
  exact BstLean.Part269.S27.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13026

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13026
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560517942015 : ℝ) ≤ plow 13026 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13026) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052415027366)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001344648454) : eMP 13026 0.011 xi bn ≤ 0.001158046100 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13026 : ℝ) * (1 - 0.011))) ≤ 0.000572632056 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001344648454 / (13026 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000572632056 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000572632056 : ℝ) + 3.141593 * 0.052415027366 / (13026 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001158046100 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052415027366)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001344648454) : PiBarMP 13026 12 0.011 xi bn ≤ 0.159200318064 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13026 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036669448510 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.502044034457 : ℝ) ≤ √((13026 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.131503100590 : ℝ) ≤ √(13026 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13026) ≤ 0.122073291636 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036669448510 + 0.052415027366 * 1.772454 / (2 * (113.502044034457 : ℝ))) * (1 + 0.001158046100) +
        8 / (13026 * 114.131503100590) + 0.122073291636 := by gcongr
    _ ≤ (0.159200318064 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052415027366)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001344648454) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280759600132) :
    parallelOracle 13026 0.011 xi bn cd ≤ 0.160165752258 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13026 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13026 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560517942015 : ℝ) ≤ plow 13026 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.131503100590 : ℝ) ≤ √(13026 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280759600132 : ℝ) / (2 * 0.560517942015 * 114.131503100590)) * 0.159200318064 +
        0.280759600132 ^ 2 / (2 * 0.560517942015 * 114.131503100590) := by gcongr
    _ ≤ (0.160165752258 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052415027366) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001344648454)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280759600132) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13026 13026 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560517942015 : ℝ) ≤ plow 13026 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.131503100590 : ℝ) ≤ √(13026 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13026 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13026 Θ 1.22 ≤ 0.011619057526 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.131503100590 := by gcongr <;> linarith
      _ ≤ (0.011619057526 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13026 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13026 13026 0.011 ≤ 0.008375311909 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13026 13026 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13026 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13026 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13026 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13026 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160165752258 + 0.011619057526 + (0.008375311909 : ℝ) *
        (1 + 2 * (0.280759600132 + 0.011619057526) / (0.560517942015 * 114.131503100590))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13026]

end BstLean.Part269.N13026

/-! The original eight local profiles supply actual 13026 moment certificates. -/
namespace BstLean.Part269.N13026
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13026 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13026 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13026 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052415027366 ∧
    0 ≤ bN 13026 BstLean.Part154.csC (groupTheta g) ∧ bN 13026 BstLean.Part154.csC (groupTheta g) ≤ 0.001344648454 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13026 13026 0.011
      (momentAllowance 13026 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13026 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13026 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13026 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13026 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13026 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228943284169 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13026 0.011
      (momentAllowance 13026 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13026 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13026
/-! The actual computed-centre upper energy formula at 13026. -/
namespace BstLean.Part269.N13026
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13026

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13026
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13026)
open BstLean.Part268 (cell13026)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084592301650
  | 2 => 0.085520085905
  | 3 => 0.086443944737
  | 4 => 0.087364810960
  | 5 => 0.088283827050
  | 6 => 0.089202378043
  | 7 => 0.090122127859
  | 8 => 0.091045059159
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13026 13026 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13026 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003224237287 + 0.003208677626 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S27.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13026

/-! Actual upper energy certificates on all 43 source endpoints at 13026. -/
namespace BstLean.Part269.N13026
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13026)
open BstLean.Part268 (cell13026)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13026 (gMinus 13026) (1 - (cell13026 i).lower) ≤ 1 ∧
    energyUpper 13026 (gMinus 13026) (BstLean.Part211.gPlus 13026)
      (finiteEnergy 13026 13026 0.011) (1 - (cell13026 i).lower) ≤
      (cell13026 i).energy := by
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
      have E := BstLean.Part269.S27.uniformEnergy10 (n := 13026) (by norm_num)
        (q := 1 - (cell13026 ⟨10,by decide⟩).lower)
        (by norm_num [cell13026]) (by norm_num [cell13026])
      exact ⟨E.1,E.2.trans (by norm_num [cell13026])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy11 (n := 13026) (by norm_num)
        (q := 1 - (cell13026 ⟨11,by decide⟩).lower)
        (by norm_num [cell13026]) (by norm_num [cell13026])
      exact ⟨E.1,E.2.trans (by norm_num [cell13026])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy12 (n := 13026) (by norm_num)
        (q := 1 - (cell13026 ⟨12,by decide⟩).lower)
        (by norm_num [cell13026]) (by norm_num [cell13026])
      exact ⟨E.1,E.2.trans (by norm_num [cell13026])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy13 (n := 13026) (by norm_num)
        (q := 1 - (cell13026 ⟨13,by decide⟩).lower)
        (by norm_num [cell13026]) (by norm_num [cell13026])
      exact ⟨E.1,E.2.trans (by norm_num [cell13026])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy14 (n := 13026) (by norm_num)
        (q := 1 - (cell13026 ⟨14,by decide⟩).lower)
        (by norm_num [cell13026]) (by norm_num [cell13026])
      exact ⟨E.1,E.2.trans (by norm_num [cell13026])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy15 (n := 13026) (by norm_num)
        (q := 1 - (cell13026 ⟨15,by decide⟩).lower)
        (by norm_num [cell13026]) (by norm_num [cell13026])
      exact ⟨E.1,E.2.trans (by norm_num [cell13026])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy16 (n := 13026) (by norm_num)
        (q := 1 - (cell13026 ⟨16,by decide⟩).lower)
        (by norm_num [cell13026]) (by norm_num [cell13026])
      exact ⟨E.1,E.2.trans (by norm_num [cell13026])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy17 (n := 13026) (by norm_num)
        (q := 1 - (cell13026 ⟨17,by decide⟩).lower)
        (by norm_num [cell13026]) (by norm_num [cell13026])
      exact ⟨E.1,E.2.trans (by norm_num [cell13026])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy18 (n := 13026) (by norm_num)
        (q := 1 - (cell13026 ⟨18,by decide⟩).lower)
        (by norm_num [cell13026]) (by norm_num [cell13026])
      exact ⟨E.1,E.2.trans (by norm_num [cell13026])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy19 (n := 13026) (by norm_num)
        (q := 1 - (cell13026 ⟨19,by decide⟩).lower)
        (by norm_num [cell13026]) (by norm_num [cell13026])
      exact ⟨E.1,E.2.trans (by norm_num [cell13026])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy20 (n := 13026) (by norm_num)
        (q := 1 - (cell13026 ⟨20,by decide⟩).lower)
        (by norm_num [cell13026]) (by norm_num [cell13026])
      exact ⟨E.1,E.2.trans (by norm_num [cell13026])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy21 (n := 13026) (by norm_num)
        (q := 1 - (cell13026 ⟨21,by decide⟩).lower)
        (by norm_num [cell13026]) (by norm_num [cell13026])
      exact ⟨E.1,E.2.trans (by norm_num [cell13026])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy22 (n := 13026) (by norm_num)
        (q := 1 - (cell13026 ⟨22,by decide⟩).lower)
        (by norm_num [cell13026]) (by norm_num [cell13026])
      exact ⟨E.1,E.2.trans (by norm_num [cell13026])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy23 (n := 13026) (by norm_num)
        (q := 1 - (cell13026 ⟨23,by decide⟩).lower)
        (by norm_num [cell13026]) (by norm_num [cell13026])
      exact ⟨E.1,E.2.trans (by norm_num [cell13026])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy24 (n := 13026) (by norm_num)
        (q := 1 - (cell13026 ⟨24,by decide⟩).lower)
        (by norm_num [cell13026]) (by norm_num [cell13026])
      exact ⟨E.1,E.2.trans (by norm_num [cell13026])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy25 (n := 13026) (by norm_num)
        (q := 1 - (cell13026 ⟨25,by decide⟩).lower)
        (by norm_num [cell13026]) (by norm_num [cell13026])
      exact ⟨E.1,E.2.trans (by norm_num [cell13026])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy26 (n := 13026) (by norm_num)
        (q := 1 - (cell13026 ⟨26,by decide⟩).lower)
        (by norm_num [cell13026]) (by norm_num [cell13026])
      exact ⟨E.1,E.2.trans (by norm_num [cell13026])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy27 (n := 13026) (by norm_num)
        (q := 1 - (cell13026 ⟨27,by decide⟩).lower)
        (by norm_num [cell13026]) (by norm_num [cell13026])
      exact ⟨E.1,E.2.trans (by norm_num [cell13026])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy28 (n := 13026) (by norm_num)
        (q := 1 - (cell13026 ⟨28,by decide⟩).lower)
        (by norm_num [cell13026]) (by norm_num [cell13026])
      exact ⟨E.1,E.2.trans (by norm_num [cell13026])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy29 (n := 13026) (by norm_num)
        (q := 1 - (cell13026 ⟨29,by decide⟩).lower)
        (by norm_num [cell13026]) (by norm_num [cell13026])
      exact ⟨E.1,E.2.trans (by norm_num [cell13026])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy30 (n := 13026) (by norm_num)
        (q := 1 - (cell13026 ⟨30,by decide⟩).lower)
        (by norm_num [cell13026]) (by norm_num [cell13026])
      exact ⟨E.1,E.2.trans (by norm_num [cell13026])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy31 (n := 13026) (by norm_num)
        (q := 1 - (cell13026 ⟨31,by decide⟩).lower)
        (by norm_num [cell13026]) (by norm_num [cell13026])
      exact ⟨E.1,E.2.trans (by norm_num [cell13026])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy32 (n := 13026) (by norm_num)
        (q := 1 - (cell13026 ⟨32,by decide⟩).lower)
        (by norm_num [cell13026]) (by norm_num [cell13026])
      exact ⟨E.1,E.2.trans (by norm_num [cell13026])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy33 (n := 13026) (by norm_num)
        (q := 1 - (cell13026 ⟨33,by decide⟩).lower)
        (by norm_num [cell13026]) (by norm_num [cell13026])
      exact ⟨E.1,E.2.trans (by norm_num [cell13026])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy34 (n := 13026) (by norm_num)
        (q := 1 - (cell13026 ⟨34,by decide⟩).lower)
        (by norm_num [cell13026]) (by norm_num [cell13026])
      exact ⟨E.1,E.2.trans (by norm_num [cell13026])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy35 (n := 13026) (by norm_num)
        (q := 1 - (cell13026 ⟨35,by decide⟩).lower)
        (by norm_num [cell13026]) (by norm_num [cell13026])
      exact ⟨E.1,E.2.trans (by norm_num [cell13026])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy36 (n := 13026) (by norm_num)
        (q := 1 - (cell13026 ⟨36,by decide⟩).lower)
        (by norm_num [cell13026]) (by norm_num [cell13026])
      exact ⟨E.1,E.2.trans (by norm_num [cell13026])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy37 (n := 13026) (by norm_num)
        (q := 1 - (cell13026 ⟨37,by decide⟩).lower)
        (by norm_num [cell13026]) (by norm_num [cell13026])
      exact ⟨E.1,E.2.trans (by norm_num [cell13026])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy38 (n := 13026) (by norm_num)
        (q := 1 - (cell13026 ⟨38,by decide⟩).lower)
        (by norm_num [cell13026]) (by norm_num [cell13026])
      exact ⟨E.1,E.2.trans (by norm_num [cell13026])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy39 (n := 13026) (by norm_num)
        (q := 1 - (cell13026 ⟨39,by decide⟩).lower)
        (by norm_num [cell13026]) (by norm_num [cell13026])
      exact ⟨E.1,E.2.trans (by norm_num [cell13026])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy40 (n := 13026) (by norm_num)
        (q := 1 - (cell13026 ⟨40,by decide⟩).lower)
        (by norm_num [cell13026]) (by norm_num [cell13026])
      exact ⟨E.1,E.2.trans (by norm_num [cell13026])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy41 (n := 13026) (by norm_num)
        (q := 1 - (cell13026 ⟨41,by decide⟩).lower)
        (by norm_num [cell13026]) (by norm_num [cell13026])
      exact ⟨E.1,E.2.trans (by norm_num [cell13026])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy42 (n := 13026) (by norm_num)
        (q := 1 - (cell13026 ⟨42,by decide⟩).lower)
        (by norm_num [cell13026]) (by norm_num [cell13026])
      exact ⟨E.1,E.2.trans (by norm_num [cell13026])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy43 (n := 13026) (by norm_num)
        (q := 1 - (cell13026 ⟨43,by decide⟩).lower)
        (by norm_num [cell13026]) (by norm_num [cell13026])
      exact ⟨E.1,E.2.trans (by norm_num [cell13026])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy44 (n := 13026) (by norm_num)
        (q := 1 - (cell13026 ⟨44,by decide⟩).lower)
        (by norm_num [cell13026]) (by norm_num [cell13026])
      exact ⟨E.1,E.2.trans (by norm_num [cell13026])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy45 (n := 13026) (by norm_num)
        (q := 1 - (cell13026 ⟨45,by decide⟩).lower)
        (by norm_num [cell13026]) (by norm_num [cell13026])
      exact ⟨E.1,E.2.trans (by norm_num [cell13026])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy46 (n := 13026) (by norm_num)
        (q := 1 - (cell13026 ⟨46,by decide⟩).lower)
        (by norm_num [cell13026]) (by norm_num [cell13026])
      exact ⟨E.1,E.2.trans (by norm_num [cell13026])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy47 (n := 13026) (by norm_num)
        (q := 1 - (cell13026 ⟨47,by decide⟩).lower)
        (by norm_num [cell13026]) (by norm_num [cell13026])
      exact ⟨E.1,E.2.trans (by norm_num [cell13026])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy48 (n := 13026) (by norm_num)
        (q := 1 - (cell13026 ⟨48,by decide⟩).lower)
        (by norm_num [cell13026]) (by norm_num [cell13026])
      exact ⟨E.1,E.2.trans (by norm_num [cell13026])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy49 (n := 13026) (by norm_num)
        (q := 1 - (cell13026 ⟨49,by decide⟩).lower)
        (by norm_num [cell13026]) (by norm_num [cell13026])
      exact ⟨E.1,E.2.trans (by norm_num [cell13026])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy50 (n := 13026) (by norm_num)
        (q := 1 - (cell13026 ⟨50,by decide⟩).lower)
        (by norm_num [cell13026]) (by norm_num [cell13026])
      exact ⟨E.1,E.2.trans (by norm_num [cell13026])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy51 (n := 13026) (by norm_num)
        (q := 1 - (cell13026 ⟨51,by decide⟩).lower)
        (by norm_num [cell13026]) (by norm_num [cell13026])
      exact ⟨E.1,E.2.trans (by norm_num [cell13026])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy52 (n := 13026) (by norm_num)
        (q := 1 - (cell13026 ⟨52,by decide⟩).lower)
        (by norm_num [cell13026]) (by norm_num [cell13026])
      exact ⟨E.1,E.2.trans (by norm_num [cell13026])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13026

/-! Source-cell containment and simple scalar guards at 13026. -/
namespace BstLean.Part269.N13026
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13026)
open BstLean.Part268 (cell13026)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13026 ⟨10,by decide⟩).lower ∧ (cell13026 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13026 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13026 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13026 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13026 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13026 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13026,cell13026,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13026 ⟨11,by decide⟩).lower ∧ (cell13026 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13026 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13026 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13026 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13026 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13026 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13026,cell13026,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13026 ⟨12,by decide⟩).lower ∧ (cell13026 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13026 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13026 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13026 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13026 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13026 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13026,cell13026,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13026 ⟨13,by decide⟩).lower ∧ (cell13026 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13026 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13026 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13026 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13026 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13026 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13026,cell13026,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13026 ⟨14,by decide⟩).lower ∧ (cell13026 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13026 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13026 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13026 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13026 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13026 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13026,cell13026,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13026 ⟨15,by decide⟩).lower ∧ (cell13026 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13026 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13026 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13026 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13026 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13026 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13026,cell13026,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13026 ⟨16,by decide⟩).lower ∧ (cell13026 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13026 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13026 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13026 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13026 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13026 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13026,cell13026,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13026 ⟨17,by decide⟩).lower ∧ (cell13026 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13026 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13026 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13026 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13026 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13026 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13026,cell13026,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13026 ⟨18,by decide⟩).lower ∧ (cell13026 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13026 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13026 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13026 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13026 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13026 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13026,cell13026,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13026 ⟨19,by decide⟩).lower ∧ (cell13026 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13026 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13026 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13026 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13026 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13026 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13026,cell13026,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13026 ⟨20,by decide⟩).lower ∧ (cell13026 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13026 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13026 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13026 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13026 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13026 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13026,cell13026,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13026 ⟨21,by decide⟩).lower ∧ (cell13026 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13026 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13026 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13026 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13026 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13026 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13026,cell13026,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13026 ⟨22,by decide⟩).lower ∧ (cell13026 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13026 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13026 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13026 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13026 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13026 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13026,cell13026,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13026 ⟨23,by decide⟩).lower ∧ (cell13026 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13026 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13026 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13026 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13026 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13026 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13026,cell13026,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13026 ⟨24,by decide⟩).lower ∧ (cell13026 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13026 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13026 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13026 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13026 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13026 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13026,cell13026,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13026 ⟨25,by decide⟩).lower ∧ (cell13026 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13026 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13026 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13026 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13026 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13026 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13026,cell13026,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13026 ⟨26,by decide⟩).lower ∧ (cell13026 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13026 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13026 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13026 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13026 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13026 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13026,cell13026,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13026 ⟨27,by decide⟩).lower ∧ (cell13026 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13026 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13026 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13026 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13026 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13026 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13026,cell13026,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13026 ⟨28,by decide⟩).lower ∧ (cell13026 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13026 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13026 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13026 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13026 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13026 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13026,cell13026,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13026 ⟨29,by decide⟩).lower ∧ (cell13026 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13026 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13026 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13026 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13026 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13026 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13026,cell13026,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13026 ⟨30,by decide⟩).lower ∧ (cell13026 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13026 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13026 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13026 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13026 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13026 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13026,cell13026,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13026 ⟨31,by decide⟩).lower ∧ (cell13026 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13026 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13026 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13026 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13026 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13026 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13026,cell13026,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13026 ⟨32,by decide⟩).lower ∧ (cell13026 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13026 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13026 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13026 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13026 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13026 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13026,cell13026,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13026 ⟨33,by decide⟩).lower ∧ (cell13026 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13026 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13026 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13026 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13026 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13026 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13026,cell13026,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13026 ⟨34,by decide⟩).lower ∧ (cell13026 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13026 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13026 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13026 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13026 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13026 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13026,cell13026,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13026 ⟨35,by decide⟩).lower ∧ (cell13026 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13026 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13026 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13026 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13026 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13026 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13026,cell13026,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13026 ⟨36,by decide⟩).lower ∧ (cell13026 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13026 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13026 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13026 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13026 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13026 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13026,cell13026,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13026 ⟨37,by decide⟩).lower ∧ (cell13026 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13026 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13026 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13026 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13026 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13026 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13026,cell13026,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13026 ⟨38,by decide⟩).lower ∧ (cell13026 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13026 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13026 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13026 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13026 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13026 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13026,cell13026,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13026 ⟨39,by decide⟩).lower ∧ (cell13026 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13026 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13026 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13026 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13026 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13026 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13026,cell13026,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13026 ⟨40,by decide⟩).lower ∧ (cell13026 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13026 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13026 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13026 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13026 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13026 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13026,cell13026,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13026 ⟨41,by decide⟩).lower ∧ (cell13026 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13026 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13026 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13026 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13026 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13026 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13026,cell13026,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13026 ⟨42,by decide⟩).lower ∧ (cell13026 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13026 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13026 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13026 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13026 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13026 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13026,cell13026,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13026 ⟨43,by decide⟩).lower ∧ (cell13026 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13026 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13026 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13026 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13026 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13026 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13026,cell13026,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13026 ⟨44,by decide⟩).lower ∧ (cell13026 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13026 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13026 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13026 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13026 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13026 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13026,cell13026,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13026 ⟨45,by decide⟩).lower ∧ (cell13026 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13026 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13026 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13026 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13026 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13026 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13026,cell13026,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13026 ⟨46,by decide⟩).lower ∧ (cell13026 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13026 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13026 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13026 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13026 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13026 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13026,cell13026,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13026 ⟨47,by decide⟩).lower ∧ (cell13026 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13026 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13026 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13026 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13026 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13026 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13026,cell13026,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13026 ⟨48,by decide⟩).lower ∧ (cell13026 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13026 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13026 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13026 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13026 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13026 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13026,cell13026,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13026 ⟨49,by decide⟩).lower ∧ (cell13026 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13026 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13026 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13026 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13026 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13026 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13026,cell13026,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13026 ⟨50,by decide⟩).lower ∧ (cell13026 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13026 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13026 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13026 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13026 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13026 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13026,cell13026,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13026 ⟨51,by decide⟩).lower ∧ (cell13026 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13026 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13026 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13026 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13026 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13026 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13026,cell13026,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13026 ⟨52,by decide⟩).lower ∧ (cell13026 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13026 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13026 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13026 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13026 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13026 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13026,cell13026,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13026 i).lower ∧
    (cell13026 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13026 i).upper ≤ (0.532 : ℝ) ∧
    (cell13026 i).centre ≤ (0.1 : ℝ) ∧ (cell13026 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13026 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13026 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13026

/-! The local source numeric instances at 13026 have no network premises. -/
namespace BstLean.Part269.N13026
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13026)
open BstLean.Part268 (cell13026)

noncomputable def sourceNumerics13026 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13026 (cell13026 i)
      scalarRow13026.M scalarRow13026.H scalarRow13026.xi := by
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
    energy_allowance := scalarRow13026.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13026]
    centre_nonneg := (scalarRow13026.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D27.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13026])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13026
/-! Actual 13027 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13027
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13027 ≤ (1.035353000362 : ℝ) := by
  have hr : (114.135883927886 : ℝ) ≤ √(13027 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.135883927886 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13027 13027 (11 / 1000) ≤
    (0.008374990441 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13027) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.135883927886 : ℝ) ≤ √(13027 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13027)
  have hdiv : K / √(13027 : ℝ) ≤ K / 114.135883927886 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.135883927886 ≤ (0.008374990441 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13027.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13027 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13027 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13027 := gPlus_lower 13027
end BstLean.Part269.N13027

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13027
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035353000361 : ℝ) ≤ wn 13027 := by
  have hn : √(13027 : ℝ) ≤ 114.135883927887 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13027 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.135883927887 ≤ 2 / √(13027 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000245450072 : ℝ) ≤ rhoBar 13027 BstLean.Part154.csC ∧
    rhoBar 13027 BstLean.Part154.csC ≤ 0.000245450452 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035353000361 : ℝ) / (1.295212 * 13027) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035353000362 : ℝ) / (1.29521 * 13027) := by gcongr
      _ ≤ (0.000245450452 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13027 BstLean.Part154.csC) ≤ 0.000981862054 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13027 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13027 BstLean.Part154.csC) (piBar (rhoBar 13027 BstLean.Part154.csC)) ≤ 0.000187476488 ∧
    cc1 (rhoBar 13027 BstLean.Part154.csC) (piBar (rhoBar 13027 BstLean.Part154.csC)) ≤ 0.000119292580 ∧
    cc2 (rhoBar 13027 BstLean.Part154.csC) ≤ 0.000069250312 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13027 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13027 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13027 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13027 BstLean.Part154.csC * nuR (rhoBar 13027 BstLean.Part154.csC)) ≤ 0.000490915966 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000245450452 : ℝ) * 0.000981862054 := by gcongr
      _ ≤ (0.000490915966 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13027 BstLean.Part154.csC) * nuR (rhoBar 13027 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000981862054 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13027 BstLean.Part154.csC) * rhoBar 13027 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000245450452 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000245450452 / 2 + 0.399 * 0.000981862054 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000187476488 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000490915966 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119292580 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000245450452 / 1.414213562 := by gcongr
      _ ≤ (0.000069250312 : ℝ) := by norm_num

end BstLean.Part269.N13027

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13027
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13027 BstLean.Part154.csC) (piBar (rhoBar 13027 BstLean.Part154.csC)) ≤ 1.51785E-7 := by
  have hr0 : 0 ≤ rhoBar 13027 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13027 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13027 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13027 BstLean.Part154.csC) (piBar (rhoBar 13027 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13027 BstLean.Part154.csC) (piBar (rhoBar 13027 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13027 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000187476488 : ℝ) ^ 2 + 0.000119292580 ^ 2 + 3 * 0.000069250312 ^ 2 +
        2 * 0.797885 * 0.000187476488 * 0.000119292580 + 2 * 0.000187476488 * 0.000069250312 +
        4 * 0.797885 * 0.000119292580 * 0.000069250312 := by gcongr
    _ ≤ (1.51785E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13027 BstLean.Part154.csC Θ ≤ 0.002561026834 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13027 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13027 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13027 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13027 BstLean.Part154.csC) (piBar (rhoBar 13027 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13027 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035353000362 * 1.51785E-7 / (0.000245450072 : ℝ) := by gcongr
    _ ≤ 0.002561026834 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13027 BstLean.Part154.csC Θ ≤ 0.002840346867 + 0.000647131422 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13027 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13027 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13027 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035353000362 : ℝ) * ((2 * Θ * 0.000245450452 +
        (6863 / 10000) * 0.000245450452 * 13027 * 0.000981862054) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002840346867 + 0.000647131422 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13027 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13027 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13027 0.011 Θ ∧ gammaRatio 13027 0.011 Θ ≤ 0.000084379519 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13027 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035353000362 : ℝ) * 0.525 / ((1 - 0.011) * 13027) := by gcongr
      _ ≤ (0.000084379519 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13027 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13027 0.011 Θ) :=
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
    badAllowance 13027 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000383431726 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13027 BstLean.Part154.csC) 1.22 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 2 (rhoBar 13027 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13027 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13027 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13027 0.011 Θ) 1.12 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 1 (gammaRatio 13027 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13027 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13027 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13027 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13027 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035353000362 : ℝ) * 13027 *
        (1.3781E-8 / 1.1045361 + 1.6832E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000383431726 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13027 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003223778593 + 0.003208158256 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13027

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13027
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13027 BstLean.Part154.csC) (piBar (rhoBar 13027 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13027 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13027 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13027 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13027 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13027 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13027 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13027 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13027 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13027 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13027 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13027 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13027 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13027 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13027 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051814305826 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13027) ≤ 0.010463296380 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13027 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035353000362)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010463296380 + 2 * 0.737676 / 13027) := by gcongr
    _ ≤ (0.051814305826 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13027 12 ≤ 0.0015 := by
  exact BstLean.Part269.S27.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13027

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13027
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560517985000 : ℝ) ≤ plow 13027 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13027) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052414661678)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001344539088) : eMP 13027 0.011 xi bn ≤ 0.001157954497 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13027 : ℝ) * (1 - 0.011))) ≤ 0.000572586790 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001344539088 / (13027 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000572586790 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000572586790 : ℝ) + 3.141593 * 0.052414661678 / (13027 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001157954497 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052414661678)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001344539088) : PiBarMP 13027 12 0.011 xi bn ≤ 0.159194116978 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13027 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036667957238 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.506400700577 : ℝ) ≤ √((13027 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.135883927886 : ℝ) ≤ √(13027 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13027) ≤ 0.122068606150 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036667957238 + 0.052414661678 * 1.772454 / (2 * (113.506400700577 : ℝ))) * (1 + 0.001157954497) +
        8 / (13027 * 114.135883927886) + 0.122068606150 := by gcongr
    _ ≤ (0.159194116978 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052414661678)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001344539088) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280756791351) :
    parallelOracle 13027 0.011 xi bn cd ≤ 0.160159484614 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13027 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13027 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560517985000 : ℝ) ≤ plow 13027 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.135883927886 : ℝ) ≤ √(13027 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280756791351 : ℝ) / (2 * 0.560517985000 * 114.135883927886)) * 0.159194116978 +
        0.280756791351 ^ 2 / (2 * 0.560517985000 * 114.135883927886) := by gcongr
    _ ≤ (0.160159484614 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052414661678) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001344539088)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280756791351) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13027 13027 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560517985000 : ℝ) ≤ plow 13027 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.135883927886 : ℝ) ≤ √(13027 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13027 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13027 Θ 1.22 ≤ 0.011618611557 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.135883927886 := by gcongr <;> linarith
      _ ≤ (0.011618611557 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13027 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13027 13027 0.011 ≤ 0.008374990441 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13027 13027 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13027 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13027 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13027 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13027 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160159484614 + 0.011618611557 + (0.008374990441 : ℝ) *
        (1 + 2 * (0.280756791351 + 0.011618611557) / (0.560517985000 * 114.135883927886))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13027]

end BstLean.Part269.N13027

/-! The original eight local profiles supply actual 13027 moment certificates. -/
namespace BstLean.Part269.N13027
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13027 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13027 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13027 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052414661678 ∧
    0 ≤ bN 13027 BstLean.Part154.csC (groupTheta g) ∧ bN 13027 BstLean.Part154.csC (groupTheta g) ≤ 0.001344539088 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13027 13027 0.011
      (momentAllowance 13027 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13027 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13027 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13027 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13027 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13027 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228942485525 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13027 0.011
      (momentAllowance 13027 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13027 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13027
/-! The actual computed-centre upper energy formula at 13027. -/
namespace BstLean.Part269.N13027
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13027

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13027
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13027)
open BstLean.Part268 (cell13027)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084589704177
  | 2 => 0.085517454614
  | 3 => 0.086441274547
  | 4 => 0.087362095596
  | 5 => 0.088281058826
  | 6 => 0.089199547611
  | 7 => 0.090119223933
  | 8 => 0.091042068206
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13027 13027 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13027 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003224237287 + 0.003208677626 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S27.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13027

/-! Actual upper energy certificates on all 43 source endpoints at 13027. -/
namespace BstLean.Part269.N13027
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13027)
open BstLean.Part268 (cell13027)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13027 (gMinus 13027) (1 - (cell13027 i).lower) ≤ 1 ∧
    energyUpper 13027 (gMinus 13027) (BstLean.Part211.gPlus 13027)
      (finiteEnergy 13027 13027 0.011) (1 - (cell13027 i).lower) ≤
      (cell13027 i).energy := by
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
      have E := BstLean.Part269.S27.uniformEnergy10 (n := 13027) (by norm_num)
        (q := 1 - (cell13027 ⟨10,by decide⟩).lower)
        (by norm_num [cell13027]) (by norm_num [cell13027])
      exact ⟨E.1,E.2.trans (by norm_num [cell13027])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy11 (n := 13027) (by norm_num)
        (q := 1 - (cell13027 ⟨11,by decide⟩).lower)
        (by norm_num [cell13027]) (by norm_num [cell13027])
      exact ⟨E.1,E.2.trans (by norm_num [cell13027])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy12 (n := 13027) (by norm_num)
        (q := 1 - (cell13027 ⟨12,by decide⟩).lower)
        (by norm_num [cell13027]) (by norm_num [cell13027])
      exact ⟨E.1,E.2.trans (by norm_num [cell13027])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy13 (n := 13027) (by norm_num)
        (q := 1 - (cell13027 ⟨13,by decide⟩).lower)
        (by norm_num [cell13027]) (by norm_num [cell13027])
      exact ⟨E.1,E.2.trans (by norm_num [cell13027])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy14 (n := 13027) (by norm_num)
        (q := 1 - (cell13027 ⟨14,by decide⟩).lower)
        (by norm_num [cell13027]) (by norm_num [cell13027])
      exact ⟨E.1,E.2.trans (by norm_num [cell13027])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy15 (n := 13027) (by norm_num)
        (q := 1 - (cell13027 ⟨15,by decide⟩).lower)
        (by norm_num [cell13027]) (by norm_num [cell13027])
      exact ⟨E.1,E.2.trans (by norm_num [cell13027])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy16 (n := 13027) (by norm_num)
        (q := 1 - (cell13027 ⟨16,by decide⟩).lower)
        (by norm_num [cell13027]) (by norm_num [cell13027])
      exact ⟨E.1,E.2.trans (by norm_num [cell13027])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy17 (n := 13027) (by norm_num)
        (q := 1 - (cell13027 ⟨17,by decide⟩).lower)
        (by norm_num [cell13027]) (by norm_num [cell13027])
      exact ⟨E.1,E.2.trans (by norm_num [cell13027])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy18 (n := 13027) (by norm_num)
        (q := 1 - (cell13027 ⟨18,by decide⟩).lower)
        (by norm_num [cell13027]) (by norm_num [cell13027])
      exact ⟨E.1,E.2.trans (by norm_num [cell13027])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy19 (n := 13027) (by norm_num)
        (q := 1 - (cell13027 ⟨19,by decide⟩).lower)
        (by norm_num [cell13027]) (by norm_num [cell13027])
      exact ⟨E.1,E.2.trans (by norm_num [cell13027])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy20 (n := 13027) (by norm_num)
        (q := 1 - (cell13027 ⟨20,by decide⟩).lower)
        (by norm_num [cell13027]) (by norm_num [cell13027])
      exact ⟨E.1,E.2.trans (by norm_num [cell13027])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy21 (n := 13027) (by norm_num)
        (q := 1 - (cell13027 ⟨21,by decide⟩).lower)
        (by norm_num [cell13027]) (by norm_num [cell13027])
      exact ⟨E.1,E.2.trans (by norm_num [cell13027])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy22 (n := 13027) (by norm_num)
        (q := 1 - (cell13027 ⟨22,by decide⟩).lower)
        (by norm_num [cell13027]) (by norm_num [cell13027])
      exact ⟨E.1,E.2.trans (by norm_num [cell13027])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy23 (n := 13027) (by norm_num)
        (q := 1 - (cell13027 ⟨23,by decide⟩).lower)
        (by norm_num [cell13027]) (by norm_num [cell13027])
      exact ⟨E.1,E.2.trans (by norm_num [cell13027])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy24 (n := 13027) (by norm_num)
        (q := 1 - (cell13027 ⟨24,by decide⟩).lower)
        (by norm_num [cell13027]) (by norm_num [cell13027])
      exact ⟨E.1,E.2.trans (by norm_num [cell13027])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy25 (n := 13027) (by norm_num)
        (q := 1 - (cell13027 ⟨25,by decide⟩).lower)
        (by norm_num [cell13027]) (by norm_num [cell13027])
      exact ⟨E.1,E.2.trans (by norm_num [cell13027])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy26 (n := 13027) (by norm_num)
        (q := 1 - (cell13027 ⟨26,by decide⟩).lower)
        (by norm_num [cell13027]) (by norm_num [cell13027])
      exact ⟨E.1,E.2.trans (by norm_num [cell13027])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy27 (n := 13027) (by norm_num)
        (q := 1 - (cell13027 ⟨27,by decide⟩).lower)
        (by norm_num [cell13027]) (by norm_num [cell13027])
      exact ⟨E.1,E.2.trans (by norm_num [cell13027])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy28 (n := 13027) (by norm_num)
        (q := 1 - (cell13027 ⟨28,by decide⟩).lower)
        (by norm_num [cell13027]) (by norm_num [cell13027])
      exact ⟨E.1,E.2.trans (by norm_num [cell13027])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy29 (n := 13027) (by norm_num)
        (q := 1 - (cell13027 ⟨29,by decide⟩).lower)
        (by norm_num [cell13027]) (by norm_num [cell13027])
      exact ⟨E.1,E.2.trans (by norm_num [cell13027])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy30 (n := 13027) (by norm_num)
        (q := 1 - (cell13027 ⟨30,by decide⟩).lower)
        (by norm_num [cell13027]) (by norm_num [cell13027])
      exact ⟨E.1,E.2.trans (by norm_num [cell13027])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy31 (n := 13027) (by norm_num)
        (q := 1 - (cell13027 ⟨31,by decide⟩).lower)
        (by norm_num [cell13027]) (by norm_num [cell13027])
      exact ⟨E.1,E.2.trans (by norm_num [cell13027])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy32 (n := 13027) (by norm_num)
        (q := 1 - (cell13027 ⟨32,by decide⟩).lower)
        (by norm_num [cell13027]) (by norm_num [cell13027])
      exact ⟨E.1,E.2.trans (by norm_num [cell13027])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy33 (n := 13027) (by norm_num)
        (q := 1 - (cell13027 ⟨33,by decide⟩).lower)
        (by norm_num [cell13027]) (by norm_num [cell13027])
      exact ⟨E.1,E.2.trans (by norm_num [cell13027])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy34 (n := 13027) (by norm_num)
        (q := 1 - (cell13027 ⟨34,by decide⟩).lower)
        (by norm_num [cell13027]) (by norm_num [cell13027])
      exact ⟨E.1,E.2.trans (by norm_num [cell13027])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy35 (n := 13027) (by norm_num)
        (q := 1 - (cell13027 ⟨35,by decide⟩).lower)
        (by norm_num [cell13027]) (by norm_num [cell13027])
      exact ⟨E.1,E.2.trans (by norm_num [cell13027])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy36 (n := 13027) (by norm_num)
        (q := 1 - (cell13027 ⟨36,by decide⟩).lower)
        (by norm_num [cell13027]) (by norm_num [cell13027])
      exact ⟨E.1,E.2.trans (by norm_num [cell13027])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy37 (n := 13027) (by norm_num)
        (q := 1 - (cell13027 ⟨37,by decide⟩).lower)
        (by norm_num [cell13027]) (by norm_num [cell13027])
      exact ⟨E.1,E.2.trans (by norm_num [cell13027])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy38 (n := 13027) (by norm_num)
        (q := 1 - (cell13027 ⟨38,by decide⟩).lower)
        (by norm_num [cell13027]) (by norm_num [cell13027])
      exact ⟨E.1,E.2.trans (by norm_num [cell13027])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy39 (n := 13027) (by norm_num)
        (q := 1 - (cell13027 ⟨39,by decide⟩).lower)
        (by norm_num [cell13027]) (by norm_num [cell13027])
      exact ⟨E.1,E.2.trans (by norm_num [cell13027])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy40 (n := 13027) (by norm_num)
        (q := 1 - (cell13027 ⟨40,by decide⟩).lower)
        (by norm_num [cell13027]) (by norm_num [cell13027])
      exact ⟨E.1,E.2.trans (by norm_num [cell13027])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy41 (n := 13027) (by norm_num)
        (q := 1 - (cell13027 ⟨41,by decide⟩).lower)
        (by norm_num [cell13027]) (by norm_num [cell13027])
      exact ⟨E.1,E.2.trans (by norm_num [cell13027])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy42 (n := 13027) (by norm_num)
        (q := 1 - (cell13027 ⟨42,by decide⟩).lower)
        (by norm_num [cell13027]) (by norm_num [cell13027])
      exact ⟨E.1,E.2.trans (by norm_num [cell13027])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy43 (n := 13027) (by norm_num)
        (q := 1 - (cell13027 ⟨43,by decide⟩).lower)
        (by norm_num [cell13027]) (by norm_num [cell13027])
      exact ⟨E.1,E.2.trans (by norm_num [cell13027])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy44 (n := 13027) (by norm_num)
        (q := 1 - (cell13027 ⟨44,by decide⟩).lower)
        (by norm_num [cell13027]) (by norm_num [cell13027])
      exact ⟨E.1,E.2.trans (by norm_num [cell13027])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy45 (n := 13027) (by norm_num)
        (q := 1 - (cell13027 ⟨45,by decide⟩).lower)
        (by norm_num [cell13027]) (by norm_num [cell13027])
      exact ⟨E.1,E.2.trans (by norm_num [cell13027])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy46 (n := 13027) (by norm_num)
        (q := 1 - (cell13027 ⟨46,by decide⟩).lower)
        (by norm_num [cell13027]) (by norm_num [cell13027])
      exact ⟨E.1,E.2.trans (by norm_num [cell13027])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy47 (n := 13027) (by norm_num)
        (q := 1 - (cell13027 ⟨47,by decide⟩).lower)
        (by norm_num [cell13027]) (by norm_num [cell13027])
      exact ⟨E.1,E.2.trans (by norm_num [cell13027])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy48 (n := 13027) (by norm_num)
        (q := 1 - (cell13027 ⟨48,by decide⟩).lower)
        (by norm_num [cell13027]) (by norm_num [cell13027])
      exact ⟨E.1,E.2.trans (by norm_num [cell13027])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy49 (n := 13027) (by norm_num)
        (q := 1 - (cell13027 ⟨49,by decide⟩).lower)
        (by norm_num [cell13027]) (by norm_num [cell13027])
      exact ⟨E.1,E.2.trans (by norm_num [cell13027])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy50 (n := 13027) (by norm_num)
        (q := 1 - (cell13027 ⟨50,by decide⟩).lower)
        (by norm_num [cell13027]) (by norm_num [cell13027])
      exact ⟨E.1,E.2.trans (by norm_num [cell13027])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy51 (n := 13027) (by norm_num)
        (q := 1 - (cell13027 ⟨51,by decide⟩).lower)
        (by norm_num [cell13027]) (by norm_num [cell13027])
      exact ⟨E.1,E.2.trans (by norm_num [cell13027])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy52 (n := 13027) (by norm_num)
        (q := 1 - (cell13027 ⟨52,by decide⟩).lower)
        (by norm_num [cell13027]) (by norm_num [cell13027])
      exact ⟨E.1,E.2.trans (by norm_num [cell13027])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13027

/-! Source-cell containment and simple scalar guards at 13027. -/
namespace BstLean.Part269.N13027
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13027)
open BstLean.Part268 (cell13027)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13027 ⟨10,by decide⟩).lower ∧ (cell13027 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13027 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13027 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13027 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13027 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13027 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13027,cell13027,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13027 ⟨11,by decide⟩).lower ∧ (cell13027 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13027 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13027 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13027 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13027 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13027 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13027,cell13027,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13027 ⟨12,by decide⟩).lower ∧ (cell13027 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13027 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13027 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13027 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13027 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13027 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13027,cell13027,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13027 ⟨13,by decide⟩).lower ∧ (cell13027 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13027 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13027 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13027 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13027 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13027 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13027,cell13027,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13027 ⟨14,by decide⟩).lower ∧ (cell13027 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13027 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13027 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13027 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13027 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13027 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13027,cell13027,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13027 ⟨15,by decide⟩).lower ∧ (cell13027 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13027 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13027 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13027 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13027 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13027 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13027,cell13027,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13027 ⟨16,by decide⟩).lower ∧ (cell13027 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13027 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13027 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13027 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13027 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13027 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13027,cell13027,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13027 ⟨17,by decide⟩).lower ∧ (cell13027 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13027 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13027 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13027 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13027 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13027 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13027,cell13027,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13027 ⟨18,by decide⟩).lower ∧ (cell13027 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13027 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13027 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13027 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13027 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13027 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13027,cell13027,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13027 ⟨19,by decide⟩).lower ∧ (cell13027 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13027 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13027 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13027 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13027 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13027 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13027,cell13027,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13027 ⟨20,by decide⟩).lower ∧ (cell13027 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13027 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13027 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13027 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13027 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13027 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13027,cell13027,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13027 ⟨21,by decide⟩).lower ∧ (cell13027 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13027 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13027 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13027 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13027 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13027 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13027,cell13027,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13027 ⟨22,by decide⟩).lower ∧ (cell13027 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13027 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13027 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13027 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13027 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13027 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13027,cell13027,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13027 ⟨23,by decide⟩).lower ∧ (cell13027 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13027 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13027 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13027 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13027 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13027 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13027,cell13027,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13027 ⟨24,by decide⟩).lower ∧ (cell13027 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13027 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13027 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13027 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13027 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13027 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13027,cell13027,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13027 ⟨25,by decide⟩).lower ∧ (cell13027 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13027 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13027 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13027 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13027 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13027 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13027,cell13027,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13027 ⟨26,by decide⟩).lower ∧ (cell13027 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13027 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13027 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13027 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13027 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13027 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13027,cell13027,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13027 ⟨27,by decide⟩).lower ∧ (cell13027 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13027 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13027 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13027 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13027 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13027 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13027,cell13027,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13027 ⟨28,by decide⟩).lower ∧ (cell13027 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13027 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13027 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13027 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13027 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13027 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13027,cell13027,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13027 ⟨29,by decide⟩).lower ∧ (cell13027 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13027 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13027 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13027 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13027 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13027 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13027,cell13027,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13027 ⟨30,by decide⟩).lower ∧ (cell13027 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13027 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13027 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13027 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13027 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13027 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13027,cell13027,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13027 ⟨31,by decide⟩).lower ∧ (cell13027 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13027 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13027 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13027 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13027 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13027 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13027,cell13027,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13027 ⟨32,by decide⟩).lower ∧ (cell13027 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13027 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13027 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13027 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13027 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13027 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13027,cell13027,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13027 ⟨33,by decide⟩).lower ∧ (cell13027 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13027 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13027 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13027 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13027 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13027 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13027,cell13027,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13027 ⟨34,by decide⟩).lower ∧ (cell13027 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13027 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13027 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13027 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13027 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13027 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13027,cell13027,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13027 ⟨35,by decide⟩).lower ∧ (cell13027 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13027 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13027 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13027 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13027 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13027 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13027,cell13027,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13027 ⟨36,by decide⟩).lower ∧ (cell13027 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13027 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13027 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13027 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13027 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13027 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13027,cell13027,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13027 ⟨37,by decide⟩).lower ∧ (cell13027 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13027 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13027 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13027 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13027 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13027 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13027,cell13027,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13027 ⟨38,by decide⟩).lower ∧ (cell13027 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13027 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13027 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13027 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13027 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13027 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13027,cell13027,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13027 ⟨39,by decide⟩).lower ∧ (cell13027 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13027 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13027 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13027 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13027 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13027 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13027,cell13027,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13027 ⟨40,by decide⟩).lower ∧ (cell13027 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13027 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13027 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13027 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13027 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13027 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13027,cell13027,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13027 ⟨41,by decide⟩).lower ∧ (cell13027 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13027 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13027 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13027 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13027 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13027 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13027,cell13027,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13027 ⟨42,by decide⟩).lower ∧ (cell13027 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13027 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13027 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13027 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13027 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13027 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13027,cell13027,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13027 ⟨43,by decide⟩).lower ∧ (cell13027 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13027 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13027 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13027 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13027 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13027 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13027,cell13027,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13027 ⟨44,by decide⟩).lower ∧ (cell13027 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13027 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13027 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13027 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13027 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13027 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13027,cell13027,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13027 ⟨45,by decide⟩).lower ∧ (cell13027 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13027 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13027 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13027 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13027 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13027 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13027,cell13027,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13027 ⟨46,by decide⟩).lower ∧ (cell13027 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13027 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13027 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13027 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13027 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13027 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13027,cell13027,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13027 ⟨47,by decide⟩).lower ∧ (cell13027 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13027 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13027 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13027 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13027 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13027 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13027,cell13027,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13027 ⟨48,by decide⟩).lower ∧ (cell13027 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13027 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13027 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13027 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13027 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13027 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13027,cell13027,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13027 ⟨49,by decide⟩).lower ∧ (cell13027 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13027 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13027 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13027 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13027 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13027 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13027,cell13027,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13027 ⟨50,by decide⟩).lower ∧ (cell13027 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13027 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13027 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13027 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13027 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13027 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13027,cell13027,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13027 ⟨51,by decide⟩).lower ∧ (cell13027 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13027 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13027 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13027 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13027 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13027 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13027,cell13027,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13027 ⟨52,by decide⟩).lower ∧ (cell13027 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13027 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13027 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13027 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13027 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13027 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13027,cell13027,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13027 i).lower ∧
    (cell13027 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13027 i).upper ≤ (0.532 : ℝ) ∧
    (cell13027 i).centre ≤ (0.1 : ℝ) ∧ (cell13027 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13027 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13027 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13027

/-! The local source numeric instances at 13027 have no network premises. -/
namespace BstLean.Part269.N13027
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13027)
open BstLean.Part268 (cell13027)

noncomputable def sourceNumerics13027 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13027 (cell13027 i)
      scalarRow13027.M scalarRow13027.H scalarRow13027.xi := by
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
    energy_allowance := scalarRow13027.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13027]
    centre_nonneg := (scalarRow13027.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D27.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13027])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13027
/-! Actual 13028 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13028
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13028 ≤ (1.035351631744 : ℝ) := by
  have hr : (114.140264587042 : ℝ) ≤ √(13028 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.140264587042 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13028 13028 (11 / 1000) ≤
    (0.008374669010 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13028) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.140264587042 : ℝ) ≤ √(13028 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13028)
  have hdiv : K / √(13028 : ℝ) ≤ K / 114.140264587042 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.140264587042 ≤ (0.008374669010 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13028.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13028 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13028 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13028 := gPlus_lower 13028
end BstLean.Part269.N13028

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13028
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035351631743 : ℝ) ≤ wn 13028 := by
  have hn : √(13028 : ℝ) ≤ 114.140264587043 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13028 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.140264587043 ≤ 2 / √(13028 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000245430908 : ℝ) ≤ rhoBar 13028 BstLean.Part154.csC ∧
    rhoBar 13028 BstLean.Part154.csC ≤ 0.000245431288 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035351631743 : ℝ) / (1.295212 * 13028) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035351631744 : ℝ) / (1.29521 * 13028) := by gcongr
      _ ≤ (0.000245431288 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13028 BstLean.Part154.csC) ≤ 0.000981785389 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13028 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13028 BstLean.Part154.csC) (piBar (rhoBar 13028 BstLean.Part154.csC)) ≤ 0.000187461850 ∧
    cc1 (rhoBar 13028 BstLean.Part154.csC) (piBar (rhoBar 13028 BstLean.Part154.csC)) ≤ 0.000119283266 ∧
    cc2 (rhoBar 13028 BstLean.Part154.csC) ≤ 0.000069244906 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13028 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13028 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13028 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13028 BstLean.Part154.csC * nuR (rhoBar 13028 BstLean.Part154.csC)) ≤ 0.000490877636 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000245431288 : ℝ) * 0.000981785389 := by gcongr
      _ ≤ (0.000490877636 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13028 BstLean.Part154.csC) * nuR (rhoBar 13028 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000981785389 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13028 BstLean.Part154.csC) * rhoBar 13028 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000245431288 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000245431288 / 2 + 0.399 * 0.000981785389 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000187461850 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000490877636 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119283266 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000245431288 / 1.414213562 := by gcongr
      _ ≤ (0.000069244906 : ℝ) := by norm_num

end BstLean.Part269.N13028

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13028
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13028 BstLean.Part154.csC) (piBar (rhoBar 13028 BstLean.Part154.csC)) ≤ 1.51762E-7 := by
  have hr0 : 0 ≤ rhoBar 13028 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13028 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13028 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13028 BstLean.Part154.csC) (piBar (rhoBar 13028 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13028 BstLean.Part154.csC) (piBar (rhoBar 13028 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13028 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000187461850 : ℝ) ^ 2 + 0.000119283266 ^ 2 + 3 * 0.000069244906 ^ 2 +
        2 * 0.797885 * 0.000187461850 * 0.000119283266 + 2 * 0.000187461850 * 0.000069244906 +
        4 * 0.797885 * 0.000119283266 * 0.000069244906 := by gcongr
    _ ≤ (1.51762E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13028 BstLean.Part154.csC Θ ≤ 0.002560835319 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13028 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13028 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13028 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13028 BstLean.Part154.csC) (piBar (rhoBar 13028 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13028 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035351631744 * 1.51762E-7 / (0.000245430908 : ℝ) := by gcongr
    _ ≤ 0.002560835319 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13028 BstLean.Part154.csC Θ ≤ 0.002840117588 + 0.000647080040 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13028 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13028 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13028 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035351631744 : ℝ) * ((2 * Θ * 0.000245431288 +
        (6863 / 10000) * 0.000245431288 * 13028 * 0.000981785389) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002840117588 + 0.000647080040 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13028 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13028 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13028 0.011 Θ ∧ gammaRatio 13028 0.011 Θ ≤ 0.000084372930 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13028 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035351631744 : ℝ) * 0.525 / ((1 - 0.011) * 13028) := by gcongr
      _ ≤ (0.000084372930 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13028 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13028 0.011 Θ) :=
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
    badAllowance 13028 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000383431726 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13028 BstLean.Part154.csC) 1.22 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 2 (rhoBar 13028 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13028 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13028 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13028 0.011 Θ) 1.12 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 1 (gammaRatio 13028 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13028 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13028 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13028 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13028 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035351631744 : ℝ) * 13028 *
        (1.3781E-8 / 1.1045361 + 1.6832E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000383431726 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13028 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003223549314 + 0.003207915359 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13028

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13028
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13028 BstLean.Part154.csC) (piBar (rhoBar 13028 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13028 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13028 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13028 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13028 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13028 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13028 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13028 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13028 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13028 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13028 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13028 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13028 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13028 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13028 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051812295921 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13028) ≤ 0.010462894803 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13028 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035351631744)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010462894803 + 2 * 0.737676 / 13028) := by gcongr
    _ ≤ (0.051812295921 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13028 12 ≤ 0.0015 := by
  exact BstLean.Part269.S27.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13028

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13028
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560518027978 : ℝ) ≤ plow 13028 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13028) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052414304878)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001344438543) : eMP 13028 0.011 xi bn ≤ 0.001157866661 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13028 : ℝ) * (1 - 0.011))) ≤ 0.000572543406 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001344438543 / (13028 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000572543406 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000572543406 : ℝ) + 3.141593 * 0.052414304878 / (13028 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001157866661 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052414304878)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001344438543) : PiBarMP 13028 12 0.011 xi bn ≤ 0.159188037010 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13028 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036666586193 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.510757199483 : ℝ) ≤ √((13028 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.140264587042 : ℝ) ≤ √(13028 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13028) ≤ 0.122063921204 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036666586193 + 0.052414304878 * 1.772454 / (2 * (113.510757199483 : ℝ))) * (1 + 0.001157866661) +
        8 / (13028 * 114.140264587042) + 0.122063921204 := by gcongr
    _ ≤ (0.159188037010 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052414304878)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001344438543) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280754002209) :
    parallelOracle 13028 0.011 xi bn cd ≤ 0.160153338471 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13028 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13028 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560518027978 : ℝ) ≤ plow 13028 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.140264587042 : ℝ) ≤ √(13028 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280754002209 : ℝ) / (2 * 0.560518027978 * 114.140264587042)) * 0.159188037010 +
        0.280754002209 ^ 2 / (2 * 0.560518027978 * 114.140264587042) := by gcongr
    _ ≤ (0.160153338471 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052414304878) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001344438543)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280754002209) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13028 13028 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560518027978 : ℝ) ≤ plow 13028 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.140264587042 : ℝ) ≤ √(13028 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13028 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13028 Θ 1.22 ≤ 0.011618165639 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.140264587042 := by gcongr <;> linarith
      _ ≤ (0.011618165639 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13028 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13028 13028 0.011 ≤ 0.008374669010 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13028 13028 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13028 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13028 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13028 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13028 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160153338471 + 0.011618165639 + (0.008374669010 : ℝ) *
        (1 + 2 * (0.280754002209 + 0.011618165639) / (0.560518027978 * 114.140264587042))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13028]

end BstLean.Part269.N13028

/-! The original eight local profiles supply actual 13028 moment certificates. -/
namespace BstLean.Part269.N13028
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13028 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13028 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13028 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052414304878 ∧
    0 ≤ bN 13028 BstLean.Part154.csC (groupTheta g) ∧ bN 13028 BstLean.Part154.csC (groupTheta g) ≤ 0.001344438543 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13028 13028 0.011
      (momentAllowance 13028 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13028 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13028 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13028 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13028 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13028 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228941706288 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13028 0.011
      (momentAllowance 13028 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13028 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13028
/-! The actual computed-centre upper energy formula at 13028. -/
namespace BstLean.Part269.N13028
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13028

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13028
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13028)
open BstLean.Part268 (cell13028)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084587107491
  | 2 => 0.085514824137
  | 3 => 0.086438605205
  | 4 => 0.087359381124
  | 5 => 0.088278291545
  | 6 => 0.089196718186
  | 7 => 0.090116321092
  | 8 => 0.091039078429
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13028 13028 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13028 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003224237287 + 0.003208677626 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S27.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13028

/-! Actual upper energy certificates on all 43 source endpoints at 13028. -/
namespace BstLean.Part269.N13028
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13028)
open BstLean.Part268 (cell13028)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13028 (gMinus 13028) (1 - (cell13028 i).lower) ≤ 1 ∧
    energyUpper 13028 (gMinus 13028) (BstLean.Part211.gPlus 13028)
      (finiteEnergy 13028 13028 0.011) (1 - (cell13028 i).lower) ≤
      (cell13028 i).energy := by
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
      have E := BstLean.Part269.S27.uniformEnergy10 (n := 13028) (by norm_num)
        (q := 1 - (cell13028 ⟨10,by decide⟩).lower)
        (by norm_num [cell13028]) (by norm_num [cell13028])
      exact ⟨E.1,E.2.trans (by norm_num [cell13028])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy11 (n := 13028) (by norm_num)
        (q := 1 - (cell13028 ⟨11,by decide⟩).lower)
        (by norm_num [cell13028]) (by norm_num [cell13028])
      exact ⟨E.1,E.2.trans (by norm_num [cell13028])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy12 (n := 13028) (by norm_num)
        (q := 1 - (cell13028 ⟨12,by decide⟩).lower)
        (by norm_num [cell13028]) (by norm_num [cell13028])
      exact ⟨E.1,E.2.trans (by norm_num [cell13028])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy13 (n := 13028) (by norm_num)
        (q := 1 - (cell13028 ⟨13,by decide⟩).lower)
        (by norm_num [cell13028]) (by norm_num [cell13028])
      exact ⟨E.1,E.2.trans (by norm_num [cell13028])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy14 (n := 13028) (by norm_num)
        (q := 1 - (cell13028 ⟨14,by decide⟩).lower)
        (by norm_num [cell13028]) (by norm_num [cell13028])
      exact ⟨E.1,E.2.trans (by norm_num [cell13028])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy15 (n := 13028) (by norm_num)
        (q := 1 - (cell13028 ⟨15,by decide⟩).lower)
        (by norm_num [cell13028]) (by norm_num [cell13028])
      exact ⟨E.1,E.2.trans (by norm_num [cell13028])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy16 (n := 13028) (by norm_num)
        (q := 1 - (cell13028 ⟨16,by decide⟩).lower)
        (by norm_num [cell13028]) (by norm_num [cell13028])
      exact ⟨E.1,E.2.trans (by norm_num [cell13028])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy17 (n := 13028) (by norm_num)
        (q := 1 - (cell13028 ⟨17,by decide⟩).lower)
        (by norm_num [cell13028]) (by norm_num [cell13028])
      exact ⟨E.1,E.2.trans (by norm_num [cell13028])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy18 (n := 13028) (by norm_num)
        (q := 1 - (cell13028 ⟨18,by decide⟩).lower)
        (by norm_num [cell13028]) (by norm_num [cell13028])
      exact ⟨E.1,E.2.trans (by norm_num [cell13028])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy19 (n := 13028) (by norm_num)
        (q := 1 - (cell13028 ⟨19,by decide⟩).lower)
        (by norm_num [cell13028]) (by norm_num [cell13028])
      exact ⟨E.1,E.2.trans (by norm_num [cell13028])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy20 (n := 13028) (by norm_num)
        (q := 1 - (cell13028 ⟨20,by decide⟩).lower)
        (by norm_num [cell13028]) (by norm_num [cell13028])
      exact ⟨E.1,E.2.trans (by norm_num [cell13028])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy21 (n := 13028) (by norm_num)
        (q := 1 - (cell13028 ⟨21,by decide⟩).lower)
        (by norm_num [cell13028]) (by norm_num [cell13028])
      exact ⟨E.1,E.2.trans (by norm_num [cell13028])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy22 (n := 13028) (by norm_num)
        (q := 1 - (cell13028 ⟨22,by decide⟩).lower)
        (by norm_num [cell13028]) (by norm_num [cell13028])
      exact ⟨E.1,E.2.trans (by norm_num [cell13028])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy23 (n := 13028) (by norm_num)
        (q := 1 - (cell13028 ⟨23,by decide⟩).lower)
        (by norm_num [cell13028]) (by norm_num [cell13028])
      exact ⟨E.1,E.2.trans (by norm_num [cell13028])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy24 (n := 13028) (by norm_num)
        (q := 1 - (cell13028 ⟨24,by decide⟩).lower)
        (by norm_num [cell13028]) (by norm_num [cell13028])
      exact ⟨E.1,E.2.trans (by norm_num [cell13028])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy25 (n := 13028) (by norm_num)
        (q := 1 - (cell13028 ⟨25,by decide⟩).lower)
        (by norm_num [cell13028]) (by norm_num [cell13028])
      exact ⟨E.1,E.2.trans (by norm_num [cell13028])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy26 (n := 13028) (by norm_num)
        (q := 1 - (cell13028 ⟨26,by decide⟩).lower)
        (by norm_num [cell13028]) (by norm_num [cell13028])
      exact ⟨E.1,E.2.trans (by norm_num [cell13028])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy27 (n := 13028) (by norm_num)
        (q := 1 - (cell13028 ⟨27,by decide⟩).lower)
        (by norm_num [cell13028]) (by norm_num [cell13028])
      exact ⟨E.1,E.2.trans (by norm_num [cell13028])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy28 (n := 13028) (by norm_num)
        (q := 1 - (cell13028 ⟨28,by decide⟩).lower)
        (by norm_num [cell13028]) (by norm_num [cell13028])
      exact ⟨E.1,E.2.trans (by norm_num [cell13028])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy29 (n := 13028) (by norm_num)
        (q := 1 - (cell13028 ⟨29,by decide⟩).lower)
        (by norm_num [cell13028]) (by norm_num [cell13028])
      exact ⟨E.1,E.2.trans (by norm_num [cell13028])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy30 (n := 13028) (by norm_num)
        (q := 1 - (cell13028 ⟨30,by decide⟩).lower)
        (by norm_num [cell13028]) (by norm_num [cell13028])
      exact ⟨E.1,E.2.trans (by norm_num [cell13028])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy31 (n := 13028) (by norm_num)
        (q := 1 - (cell13028 ⟨31,by decide⟩).lower)
        (by norm_num [cell13028]) (by norm_num [cell13028])
      exact ⟨E.1,E.2.trans (by norm_num [cell13028])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy32 (n := 13028) (by norm_num)
        (q := 1 - (cell13028 ⟨32,by decide⟩).lower)
        (by norm_num [cell13028]) (by norm_num [cell13028])
      exact ⟨E.1,E.2.trans (by norm_num [cell13028])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy33 (n := 13028) (by norm_num)
        (q := 1 - (cell13028 ⟨33,by decide⟩).lower)
        (by norm_num [cell13028]) (by norm_num [cell13028])
      exact ⟨E.1,E.2.trans (by norm_num [cell13028])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy34 (n := 13028) (by norm_num)
        (q := 1 - (cell13028 ⟨34,by decide⟩).lower)
        (by norm_num [cell13028]) (by norm_num [cell13028])
      exact ⟨E.1,E.2.trans (by norm_num [cell13028])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy35 (n := 13028) (by norm_num)
        (q := 1 - (cell13028 ⟨35,by decide⟩).lower)
        (by norm_num [cell13028]) (by norm_num [cell13028])
      exact ⟨E.1,E.2.trans (by norm_num [cell13028])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy36 (n := 13028) (by norm_num)
        (q := 1 - (cell13028 ⟨36,by decide⟩).lower)
        (by norm_num [cell13028]) (by norm_num [cell13028])
      exact ⟨E.1,E.2.trans (by norm_num [cell13028])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy37 (n := 13028) (by norm_num)
        (q := 1 - (cell13028 ⟨37,by decide⟩).lower)
        (by norm_num [cell13028]) (by norm_num [cell13028])
      exact ⟨E.1,E.2.trans (by norm_num [cell13028])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy38 (n := 13028) (by norm_num)
        (q := 1 - (cell13028 ⟨38,by decide⟩).lower)
        (by norm_num [cell13028]) (by norm_num [cell13028])
      exact ⟨E.1,E.2.trans (by norm_num [cell13028])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy39 (n := 13028) (by norm_num)
        (q := 1 - (cell13028 ⟨39,by decide⟩).lower)
        (by norm_num [cell13028]) (by norm_num [cell13028])
      exact ⟨E.1,E.2.trans (by norm_num [cell13028])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy40 (n := 13028) (by norm_num)
        (q := 1 - (cell13028 ⟨40,by decide⟩).lower)
        (by norm_num [cell13028]) (by norm_num [cell13028])
      exact ⟨E.1,E.2.trans (by norm_num [cell13028])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy41 (n := 13028) (by norm_num)
        (q := 1 - (cell13028 ⟨41,by decide⟩).lower)
        (by norm_num [cell13028]) (by norm_num [cell13028])
      exact ⟨E.1,E.2.trans (by norm_num [cell13028])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy42 (n := 13028) (by norm_num)
        (q := 1 - (cell13028 ⟨42,by decide⟩).lower)
        (by norm_num [cell13028]) (by norm_num [cell13028])
      exact ⟨E.1,E.2.trans (by norm_num [cell13028])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy43 (n := 13028) (by norm_num)
        (q := 1 - (cell13028 ⟨43,by decide⟩).lower)
        (by norm_num [cell13028]) (by norm_num [cell13028])
      exact ⟨E.1,E.2.trans (by norm_num [cell13028])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy44 (n := 13028) (by norm_num)
        (q := 1 - (cell13028 ⟨44,by decide⟩).lower)
        (by norm_num [cell13028]) (by norm_num [cell13028])
      exact ⟨E.1,E.2.trans (by norm_num [cell13028])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy45 (n := 13028) (by norm_num)
        (q := 1 - (cell13028 ⟨45,by decide⟩).lower)
        (by norm_num [cell13028]) (by norm_num [cell13028])
      exact ⟨E.1,E.2.trans (by norm_num [cell13028])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy46 (n := 13028) (by norm_num)
        (q := 1 - (cell13028 ⟨46,by decide⟩).lower)
        (by norm_num [cell13028]) (by norm_num [cell13028])
      exact ⟨E.1,E.2.trans (by norm_num [cell13028])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy47 (n := 13028) (by norm_num)
        (q := 1 - (cell13028 ⟨47,by decide⟩).lower)
        (by norm_num [cell13028]) (by norm_num [cell13028])
      exact ⟨E.1,E.2.trans (by norm_num [cell13028])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy48 (n := 13028) (by norm_num)
        (q := 1 - (cell13028 ⟨48,by decide⟩).lower)
        (by norm_num [cell13028]) (by norm_num [cell13028])
      exact ⟨E.1,E.2.trans (by norm_num [cell13028])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy49 (n := 13028) (by norm_num)
        (q := 1 - (cell13028 ⟨49,by decide⟩).lower)
        (by norm_num [cell13028]) (by norm_num [cell13028])
      exact ⟨E.1,E.2.trans (by norm_num [cell13028])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy50 (n := 13028) (by norm_num)
        (q := 1 - (cell13028 ⟨50,by decide⟩).lower)
        (by norm_num [cell13028]) (by norm_num [cell13028])
      exact ⟨E.1,E.2.trans (by norm_num [cell13028])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy51 (n := 13028) (by norm_num)
        (q := 1 - (cell13028 ⟨51,by decide⟩).lower)
        (by norm_num [cell13028]) (by norm_num [cell13028])
      exact ⟨E.1,E.2.trans (by norm_num [cell13028])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy52 (n := 13028) (by norm_num)
        (q := 1 - (cell13028 ⟨52,by decide⟩).lower)
        (by norm_num [cell13028]) (by norm_num [cell13028])
      exact ⟨E.1,E.2.trans (by norm_num [cell13028])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13028

/-! Source-cell containment and simple scalar guards at 13028. -/
namespace BstLean.Part269.N13028
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13028)
open BstLean.Part268 (cell13028)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13028 ⟨10,by decide⟩).lower ∧ (cell13028 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13028 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13028 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13028 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13028 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13028 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13028,cell13028,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13028 ⟨11,by decide⟩).lower ∧ (cell13028 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13028 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13028 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13028 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13028 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13028 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13028,cell13028,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13028 ⟨12,by decide⟩).lower ∧ (cell13028 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13028 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13028 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13028 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13028 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13028 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13028,cell13028,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13028 ⟨13,by decide⟩).lower ∧ (cell13028 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13028 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13028 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13028 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13028 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13028 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13028,cell13028,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13028 ⟨14,by decide⟩).lower ∧ (cell13028 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13028 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13028 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13028 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13028 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13028 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13028,cell13028,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13028 ⟨15,by decide⟩).lower ∧ (cell13028 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13028 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13028 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13028 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13028 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13028 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13028,cell13028,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13028 ⟨16,by decide⟩).lower ∧ (cell13028 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13028 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13028 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13028 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13028 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13028 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13028,cell13028,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13028 ⟨17,by decide⟩).lower ∧ (cell13028 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13028 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13028 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13028 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13028 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13028 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13028,cell13028,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13028 ⟨18,by decide⟩).lower ∧ (cell13028 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13028 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13028 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13028 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13028 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13028 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13028,cell13028,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13028 ⟨19,by decide⟩).lower ∧ (cell13028 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13028 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13028 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13028 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13028 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13028 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13028,cell13028,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13028 ⟨20,by decide⟩).lower ∧ (cell13028 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13028 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13028 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13028 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13028 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13028 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13028,cell13028,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13028 ⟨21,by decide⟩).lower ∧ (cell13028 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13028 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13028 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13028 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13028 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13028 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13028,cell13028,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13028 ⟨22,by decide⟩).lower ∧ (cell13028 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13028 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13028 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13028 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13028 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13028 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13028,cell13028,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13028 ⟨23,by decide⟩).lower ∧ (cell13028 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13028 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13028 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13028 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13028 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13028 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13028,cell13028,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13028 ⟨24,by decide⟩).lower ∧ (cell13028 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13028 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13028 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13028 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13028 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13028 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13028,cell13028,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13028 ⟨25,by decide⟩).lower ∧ (cell13028 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13028 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13028 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13028 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13028 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13028 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13028,cell13028,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13028 ⟨26,by decide⟩).lower ∧ (cell13028 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13028 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13028 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13028 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13028 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13028 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13028,cell13028,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13028 ⟨27,by decide⟩).lower ∧ (cell13028 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13028 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13028 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13028 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13028 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13028 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13028,cell13028,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13028 ⟨28,by decide⟩).lower ∧ (cell13028 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13028 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13028 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13028 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13028 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13028 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13028,cell13028,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13028 ⟨29,by decide⟩).lower ∧ (cell13028 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13028 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13028 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13028 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13028 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13028 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13028,cell13028,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13028 ⟨30,by decide⟩).lower ∧ (cell13028 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13028 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13028 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13028 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13028 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13028 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13028,cell13028,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13028 ⟨31,by decide⟩).lower ∧ (cell13028 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13028 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13028 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13028 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13028 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13028 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13028,cell13028,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13028 ⟨32,by decide⟩).lower ∧ (cell13028 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13028 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13028 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13028 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13028 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13028 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13028,cell13028,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13028 ⟨33,by decide⟩).lower ∧ (cell13028 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13028 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13028 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13028 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13028 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13028 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13028,cell13028,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13028 ⟨34,by decide⟩).lower ∧ (cell13028 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13028 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13028 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13028 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13028 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13028 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13028,cell13028,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13028 ⟨35,by decide⟩).lower ∧ (cell13028 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13028 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13028 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13028 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13028 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13028 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13028,cell13028,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13028 ⟨36,by decide⟩).lower ∧ (cell13028 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13028 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13028 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13028 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13028 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13028 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13028,cell13028,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13028 ⟨37,by decide⟩).lower ∧ (cell13028 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13028 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13028 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13028 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13028 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13028 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13028,cell13028,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13028 ⟨38,by decide⟩).lower ∧ (cell13028 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13028 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13028 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13028 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13028 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13028 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13028,cell13028,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13028 ⟨39,by decide⟩).lower ∧ (cell13028 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13028 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13028 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13028 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13028 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13028 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13028,cell13028,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13028 ⟨40,by decide⟩).lower ∧ (cell13028 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13028 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13028 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13028 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13028 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13028 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13028,cell13028,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13028 ⟨41,by decide⟩).lower ∧ (cell13028 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13028 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13028 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13028 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13028 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13028 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13028,cell13028,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13028 ⟨42,by decide⟩).lower ∧ (cell13028 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13028 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13028 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13028 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13028 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13028 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13028,cell13028,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13028 ⟨43,by decide⟩).lower ∧ (cell13028 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13028 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13028 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13028 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13028 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13028 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13028,cell13028,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13028 ⟨44,by decide⟩).lower ∧ (cell13028 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13028 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13028 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13028 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13028 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13028 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13028,cell13028,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13028 ⟨45,by decide⟩).lower ∧ (cell13028 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13028 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13028 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13028 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13028 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13028 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13028,cell13028,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13028 ⟨46,by decide⟩).lower ∧ (cell13028 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13028 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13028 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13028 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13028 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13028 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13028,cell13028,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13028 ⟨47,by decide⟩).lower ∧ (cell13028 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13028 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13028 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13028 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13028 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13028 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13028,cell13028,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13028 ⟨48,by decide⟩).lower ∧ (cell13028 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13028 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13028 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13028 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13028 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13028 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13028,cell13028,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13028 ⟨49,by decide⟩).lower ∧ (cell13028 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13028 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13028 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13028 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13028 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13028 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13028,cell13028,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13028 ⟨50,by decide⟩).lower ∧ (cell13028 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13028 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13028 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13028 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13028 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13028 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13028,cell13028,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13028 ⟨51,by decide⟩).lower ∧ (cell13028 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13028 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13028 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13028 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13028 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13028 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13028,cell13028,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13028 ⟨52,by decide⟩).lower ∧ (cell13028 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13028 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13028 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13028 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13028 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13028 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13028,cell13028,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13028 i).lower ∧
    (cell13028 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13028 i).upper ≤ (0.532 : ℝ) ∧
    (cell13028 i).centre ≤ (0.1 : ℝ) ∧ (cell13028 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13028 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13028 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13028

/-! The local source numeric instances at 13028 have no network premises. -/
namespace BstLean.Part269.N13028
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13028)
open BstLean.Part268 (cell13028)

noncomputable def sourceNumerics13028 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13028 (cell13028 i)
      scalarRow13028.M scalarRow13028.H scalarRow13028.xi := by
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
    energy_allowance := scalarRow13028.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13028]
    centre_nonneg := (scalarRow13028.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D27.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13028])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13028
/-! Actual 13029 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13029
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13029 ≤ (1.035350263283 : ℝ) := by
  have hr : (114.144645078076 : ℝ) ≤ √(13029 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.144645078076 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13029 13029 (11 / 1000) ≤
    (0.008374347615 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13029) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.144645078076 : ℝ) ≤ √(13029 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13029)
  have hdiv : K / √(13029 : ℝ) ≤ K / 114.144645078076 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.144645078076 ≤ (0.008374347615 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13029.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13029 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13029 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13029 := gPlus_lower 13029
end BstLean.Part269.N13029

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13029
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035350263282 : ℝ) ≤ wn 13029 := by
  have hn : √(13029 : ℝ) ≤ 114.144645078077 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13029 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.144645078077 ≤ 2 / √(13029 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000245411746 : ℝ) ≤ rhoBar 13029 BstLean.Part154.csC ∧
    rhoBar 13029 BstLean.Part154.csC ≤ 0.000245412126 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035350263282 : ℝ) / (1.295212 * 13029) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035350263283 : ℝ) / (1.29521 * 13029) := by gcongr
      _ ≤ (0.000245412126 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13029 BstLean.Part154.csC) ≤ 0.000981708732 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13029 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13029 BstLean.Part154.csC) (piBar (rhoBar 13029 BstLean.Part154.csC)) ≤ 0.000187447214 ∧
    cc1 (rhoBar 13029 BstLean.Part154.csC) (piBar (rhoBar 13029 BstLean.Part154.csC)) ≤ 0.000119273953 ∧
    cc2 (rhoBar 13029 BstLean.Part154.csC) ≤ 0.000069239499 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13029 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13029 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13029 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13029 BstLean.Part154.csC * nuR (rhoBar 13029 BstLean.Part154.csC)) ≤ 0.000490839309 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000245412126 : ℝ) * 0.000981708732 := by gcongr
      _ ≤ (0.000490839309 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13029 BstLean.Part154.csC) * nuR (rhoBar 13029 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000981708732 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13029 BstLean.Part154.csC) * rhoBar 13029 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000245412126 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000245412126 / 2 + 0.399 * 0.000981708732 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000187447214 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000490839309 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119273953 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000245412126 / 1.414213562 := by gcongr
      _ ≤ (0.000069239499 : ℝ) := by norm_num

end BstLean.Part269.N13029

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13029
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13029 BstLean.Part154.csC) (piBar (rhoBar 13029 BstLean.Part154.csC)) ≤ 1.51738E-7 := by
  have hr0 : 0 ≤ rhoBar 13029 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13029 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13029 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13029 BstLean.Part154.csC) (piBar (rhoBar 13029 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13029 BstLean.Part154.csC) (piBar (rhoBar 13029 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13029 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000187447214 : ℝ) ^ 2 + 0.000119273953 ^ 2 + 3 * 0.000069239499 ^ 2 +
        2 * 0.797885 * 0.000187447214 * 0.000119273953 + 2 * 0.000187447214 * 0.000069239499 +
        4 * 0.797885 * 0.000119273953 * 0.000069239499 := by gcongr
    _ ≤ (1.51738E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13029 BstLean.Part154.csC Θ ≤ 0.002560626879 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13029 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13029 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13029 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13029 BstLean.Part154.csC) (piBar (rhoBar 13029 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13029 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035350263283 * 1.51738E-7 / (0.000245411746 : ℝ) := by gcongr
    _ ≤ 0.002560626879 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13029 BstLean.Part154.csC Θ ≤ 0.002839888323 + 0.000647028664 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13029 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13029 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13029 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035350263283 : ℝ) * ((2 * Θ * 0.000245412126 +
        (6863 / 10000) * 0.000245412126 * 13029 * 0.000981708732) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002839888323 + 0.000647028664 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13029 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13029 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13029 0.011 Θ ∧ gammaRatio 13029 0.011 Θ ≤ 0.000084366343 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13029 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035350263283 : ℝ) * 0.525 / ((1 - 0.011) * 13029) := by gcongr
      _ ≤ (0.000084366343 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13029 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13029 0.011 Θ) :=
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
    badAllowance 13029 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000383431726 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13029 BstLean.Part154.csC) 1.22 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 2 (rhoBar 13029 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13029 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13029 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13029 0.011 Θ) 1.12 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 1 (gammaRatio 13029 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13029 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13029 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13029 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13029 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035350263283 : ℝ) * 13029 *
        (1.3781E-8 / 1.1045361 + 1.6832E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000383431726 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13029 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003223320049 + 0.003207655543 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13029

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13029
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13029 BstLean.Part154.csC) (piBar (rhoBar 13029 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13029 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13029 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13029 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13029 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13029 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13029 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13029 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13029 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13029 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13029 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13029 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13029 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13029 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13029 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051810286248 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13029) ≤ 0.010462493272 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13029 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035350263283)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010462493272 + 2 * 0.737676 / 13029) := by gcongr
    _ ≤ (0.051810286248 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13029 12 ≤ 0.0015 := by
  exact BstLean.Part269.S27.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13029

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13029
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560518070949 : ℝ) ≤ plow 13029 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13029) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052413939210)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001344329112) : eMP 13029 0.011 xi bn ≤ 0.001157775045 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13029 : ℝ) * (1 - 0.011))) ≤ 0.000572498133 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001344329112 / (13029 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000572498133 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000572498133 : ℝ) + 3.141593 * 0.052413939210 / (13029 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001157775045 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052413939210)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001344329112) : PiBarMP 13029 12 0.011 xi bn ≤ 0.159181836004 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13029 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036665093918 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.515113531194 : ℝ) ≤ √((13029 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.144645078076 : ℝ) ≤ √(13029 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13029) ≤ 0.122059236798 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036665093918 + 0.052413939210 * 1.772454 / (2 * (113.515113531194 : ℝ))) * (1 + 0.001157775045) +
        8 / (13029 * 114.144645078076) + 0.122059236798 := by gcongr
    _ ≤ (0.159181836004 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052413939210)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001344329112) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280751193930) :
    parallelOracle 13029 0.011 xi bn cd ≤ 0.160147070924 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13029 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13029 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560518070949 : ℝ) ≤ plow 13029 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.144645078076 : ℝ) ≤ √(13029 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280751193930 : ℝ) / (2 * 0.560518070949 * 114.144645078076)) * 0.159181836004 +
        0.280751193930 ^ 2 / (2 * 0.560518070949 * 114.144645078076) := by gcongr
    _ ≤ (0.160147070924 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052413939210) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001344329112)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280751193930) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13029 13029 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560518070949 : ℝ) ≤ plow 13029 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.144645078076 : ℝ) ≤ √(13029 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13029 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13029 Θ 1.22 ≤ 0.011617719773 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.144645078076 := by gcongr <;> linarith
      _ ≤ (0.011617719773 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13029 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13029 13029 0.011 ≤ 0.008374347615 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13029 13029 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13029 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13029 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13029 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13029 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160147070924 + 0.011617719773 + (0.008374347615 : ℝ) *
        (1 + 2 * (0.280751193930 + 0.011617719773) / (0.560518070949 * 114.144645078076))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13029]

end BstLean.Part269.N13029

/-! The original eight local profiles supply actual 13029 moment certificates. -/
namespace BstLean.Part269.N13029
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13029 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13029 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13029 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052413939210 ∧
    0 ≤ bN 13029 BstLean.Part154.csC (groupTheta g) ∧ bN 13029 BstLean.Part154.csC (groupTheta g) ≤ 0.001344329112 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13029 13029 0.011
      (momentAllowance 13029 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13029 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13029 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13029 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13029 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13029 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228940907682 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13029 0.011
      (momentAllowance 13029 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13029 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13029
/-! The actual computed-centre upper energy formula at 13029. -/
namespace BstLean.Part269.N13029
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13029

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13029
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13029)
open BstLean.Part268 (cell13029)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084584511592
  | 2 => 0.085512194475
  | 3 => 0.086435936713
  | 4 => 0.087356667542
  | 5 => 0.088275525207
  | 6 => 0.089193889766
  | 7 => 0.090113419333
  | 8 => 0.091036089828
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13029 13029 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13029 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003224237287 + 0.003208677626 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S27.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13029

/-! Actual upper energy certificates on all 43 source endpoints at 13029. -/
namespace BstLean.Part269.N13029
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13029)
open BstLean.Part268 (cell13029)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13029 (gMinus 13029) (1 - (cell13029 i).lower) ≤ 1 ∧
    energyUpper 13029 (gMinus 13029) (BstLean.Part211.gPlus 13029)
      (finiteEnergy 13029 13029 0.011) (1 - (cell13029 i).lower) ≤
      (cell13029 i).energy := by
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
      have E := BstLean.Part269.S27.uniformEnergy10 (n := 13029) (by norm_num)
        (q := 1 - (cell13029 ⟨10,by decide⟩).lower)
        (by norm_num [cell13029]) (by norm_num [cell13029])
      exact ⟨E.1,E.2.trans (by norm_num [cell13029])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy11 (n := 13029) (by norm_num)
        (q := 1 - (cell13029 ⟨11,by decide⟩).lower)
        (by norm_num [cell13029]) (by norm_num [cell13029])
      exact ⟨E.1,E.2.trans (by norm_num [cell13029])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy12 (n := 13029) (by norm_num)
        (q := 1 - (cell13029 ⟨12,by decide⟩).lower)
        (by norm_num [cell13029]) (by norm_num [cell13029])
      exact ⟨E.1,E.2.trans (by norm_num [cell13029])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy13 (n := 13029) (by norm_num)
        (q := 1 - (cell13029 ⟨13,by decide⟩).lower)
        (by norm_num [cell13029]) (by norm_num [cell13029])
      exact ⟨E.1,E.2.trans (by norm_num [cell13029])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy14 (n := 13029) (by norm_num)
        (q := 1 - (cell13029 ⟨14,by decide⟩).lower)
        (by norm_num [cell13029]) (by norm_num [cell13029])
      exact ⟨E.1,E.2.trans (by norm_num [cell13029])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy15 (n := 13029) (by norm_num)
        (q := 1 - (cell13029 ⟨15,by decide⟩).lower)
        (by norm_num [cell13029]) (by norm_num [cell13029])
      exact ⟨E.1,E.2.trans (by norm_num [cell13029])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy16 (n := 13029) (by norm_num)
        (q := 1 - (cell13029 ⟨16,by decide⟩).lower)
        (by norm_num [cell13029]) (by norm_num [cell13029])
      exact ⟨E.1,E.2.trans (by norm_num [cell13029])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy17 (n := 13029) (by norm_num)
        (q := 1 - (cell13029 ⟨17,by decide⟩).lower)
        (by norm_num [cell13029]) (by norm_num [cell13029])
      exact ⟨E.1,E.2.trans (by norm_num [cell13029])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy18 (n := 13029) (by norm_num)
        (q := 1 - (cell13029 ⟨18,by decide⟩).lower)
        (by norm_num [cell13029]) (by norm_num [cell13029])
      exact ⟨E.1,E.2.trans (by norm_num [cell13029])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy19 (n := 13029) (by norm_num)
        (q := 1 - (cell13029 ⟨19,by decide⟩).lower)
        (by norm_num [cell13029]) (by norm_num [cell13029])
      exact ⟨E.1,E.2.trans (by norm_num [cell13029])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy20 (n := 13029) (by norm_num)
        (q := 1 - (cell13029 ⟨20,by decide⟩).lower)
        (by norm_num [cell13029]) (by norm_num [cell13029])
      exact ⟨E.1,E.2.trans (by norm_num [cell13029])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy21 (n := 13029) (by norm_num)
        (q := 1 - (cell13029 ⟨21,by decide⟩).lower)
        (by norm_num [cell13029]) (by norm_num [cell13029])
      exact ⟨E.1,E.2.trans (by norm_num [cell13029])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy22 (n := 13029) (by norm_num)
        (q := 1 - (cell13029 ⟨22,by decide⟩).lower)
        (by norm_num [cell13029]) (by norm_num [cell13029])
      exact ⟨E.1,E.2.trans (by norm_num [cell13029])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy23 (n := 13029) (by norm_num)
        (q := 1 - (cell13029 ⟨23,by decide⟩).lower)
        (by norm_num [cell13029]) (by norm_num [cell13029])
      exact ⟨E.1,E.2.trans (by norm_num [cell13029])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy24 (n := 13029) (by norm_num)
        (q := 1 - (cell13029 ⟨24,by decide⟩).lower)
        (by norm_num [cell13029]) (by norm_num [cell13029])
      exact ⟨E.1,E.2.trans (by norm_num [cell13029])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy25 (n := 13029) (by norm_num)
        (q := 1 - (cell13029 ⟨25,by decide⟩).lower)
        (by norm_num [cell13029]) (by norm_num [cell13029])
      exact ⟨E.1,E.2.trans (by norm_num [cell13029])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy26 (n := 13029) (by norm_num)
        (q := 1 - (cell13029 ⟨26,by decide⟩).lower)
        (by norm_num [cell13029]) (by norm_num [cell13029])
      exact ⟨E.1,E.2.trans (by norm_num [cell13029])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy27 (n := 13029) (by norm_num)
        (q := 1 - (cell13029 ⟨27,by decide⟩).lower)
        (by norm_num [cell13029]) (by norm_num [cell13029])
      exact ⟨E.1,E.2.trans (by norm_num [cell13029])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy28 (n := 13029) (by norm_num)
        (q := 1 - (cell13029 ⟨28,by decide⟩).lower)
        (by norm_num [cell13029]) (by norm_num [cell13029])
      exact ⟨E.1,E.2.trans (by norm_num [cell13029])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy29 (n := 13029) (by norm_num)
        (q := 1 - (cell13029 ⟨29,by decide⟩).lower)
        (by norm_num [cell13029]) (by norm_num [cell13029])
      exact ⟨E.1,E.2.trans (by norm_num [cell13029])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy30 (n := 13029) (by norm_num)
        (q := 1 - (cell13029 ⟨30,by decide⟩).lower)
        (by norm_num [cell13029]) (by norm_num [cell13029])
      exact ⟨E.1,E.2.trans (by norm_num [cell13029])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy31 (n := 13029) (by norm_num)
        (q := 1 - (cell13029 ⟨31,by decide⟩).lower)
        (by norm_num [cell13029]) (by norm_num [cell13029])
      exact ⟨E.1,E.2.trans (by norm_num [cell13029])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy32 (n := 13029) (by norm_num)
        (q := 1 - (cell13029 ⟨32,by decide⟩).lower)
        (by norm_num [cell13029]) (by norm_num [cell13029])
      exact ⟨E.1,E.2.trans (by norm_num [cell13029])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy33 (n := 13029) (by norm_num)
        (q := 1 - (cell13029 ⟨33,by decide⟩).lower)
        (by norm_num [cell13029]) (by norm_num [cell13029])
      exact ⟨E.1,E.2.trans (by norm_num [cell13029])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy34 (n := 13029) (by norm_num)
        (q := 1 - (cell13029 ⟨34,by decide⟩).lower)
        (by norm_num [cell13029]) (by norm_num [cell13029])
      exact ⟨E.1,E.2.trans (by norm_num [cell13029])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy35 (n := 13029) (by norm_num)
        (q := 1 - (cell13029 ⟨35,by decide⟩).lower)
        (by norm_num [cell13029]) (by norm_num [cell13029])
      exact ⟨E.1,E.2.trans (by norm_num [cell13029])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy36 (n := 13029) (by norm_num)
        (q := 1 - (cell13029 ⟨36,by decide⟩).lower)
        (by norm_num [cell13029]) (by norm_num [cell13029])
      exact ⟨E.1,E.2.trans (by norm_num [cell13029])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy37 (n := 13029) (by norm_num)
        (q := 1 - (cell13029 ⟨37,by decide⟩).lower)
        (by norm_num [cell13029]) (by norm_num [cell13029])
      exact ⟨E.1,E.2.trans (by norm_num [cell13029])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy38 (n := 13029) (by norm_num)
        (q := 1 - (cell13029 ⟨38,by decide⟩).lower)
        (by norm_num [cell13029]) (by norm_num [cell13029])
      exact ⟨E.1,E.2.trans (by norm_num [cell13029])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy39 (n := 13029) (by norm_num)
        (q := 1 - (cell13029 ⟨39,by decide⟩).lower)
        (by norm_num [cell13029]) (by norm_num [cell13029])
      exact ⟨E.1,E.2.trans (by norm_num [cell13029])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy40 (n := 13029) (by norm_num)
        (q := 1 - (cell13029 ⟨40,by decide⟩).lower)
        (by norm_num [cell13029]) (by norm_num [cell13029])
      exact ⟨E.1,E.2.trans (by norm_num [cell13029])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy41 (n := 13029) (by norm_num)
        (q := 1 - (cell13029 ⟨41,by decide⟩).lower)
        (by norm_num [cell13029]) (by norm_num [cell13029])
      exact ⟨E.1,E.2.trans (by norm_num [cell13029])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy42 (n := 13029) (by norm_num)
        (q := 1 - (cell13029 ⟨42,by decide⟩).lower)
        (by norm_num [cell13029]) (by norm_num [cell13029])
      exact ⟨E.1,E.2.trans (by norm_num [cell13029])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy43 (n := 13029) (by norm_num)
        (q := 1 - (cell13029 ⟨43,by decide⟩).lower)
        (by norm_num [cell13029]) (by norm_num [cell13029])
      exact ⟨E.1,E.2.trans (by norm_num [cell13029])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy44 (n := 13029) (by norm_num)
        (q := 1 - (cell13029 ⟨44,by decide⟩).lower)
        (by norm_num [cell13029]) (by norm_num [cell13029])
      exact ⟨E.1,E.2.trans (by norm_num [cell13029])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy45 (n := 13029) (by norm_num)
        (q := 1 - (cell13029 ⟨45,by decide⟩).lower)
        (by norm_num [cell13029]) (by norm_num [cell13029])
      exact ⟨E.1,E.2.trans (by norm_num [cell13029])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy46 (n := 13029) (by norm_num)
        (q := 1 - (cell13029 ⟨46,by decide⟩).lower)
        (by norm_num [cell13029]) (by norm_num [cell13029])
      exact ⟨E.1,E.2.trans (by norm_num [cell13029])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy47 (n := 13029) (by norm_num)
        (q := 1 - (cell13029 ⟨47,by decide⟩).lower)
        (by norm_num [cell13029]) (by norm_num [cell13029])
      exact ⟨E.1,E.2.trans (by norm_num [cell13029])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy48 (n := 13029) (by norm_num)
        (q := 1 - (cell13029 ⟨48,by decide⟩).lower)
        (by norm_num [cell13029]) (by norm_num [cell13029])
      exact ⟨E.1,E.2.trans (by norm_num [cell13029])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy49 (n := 13029) (by norm_num)
        (q := 1 - (cell13029 ⟨49,by decide⟩).lower)
        (by norm_num [cell13029]) (by norm_num [cell13029])
      exact ⟨E.1,E.2.trans (by norm_num [cell13029])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy50 (n := 13029) (by norm_num)
        (q := 1 - (cell13029 ⟨50,by decide⟩).lower)
        (by norm_num [cell13029]) (by norm_num [cell13029])
      exact ⟨E.1,E.2.trans (by norm_num [cell13029])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy51 (n := 13029) (by norm_num)
        (q := 1 - (cell13029 ⟨51,by decide⟩).lower)
        (by norm_num [cell13029]) (by norm_num [cell13029])
      exact ⟨E.1,E.2.trans (by norm_num [cell13029])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy52 (n := 13029) (by norm_num)
        (q := 1 - (cell13029 ⟨52,by decide⟩).lower)
        (by norm_num [cell13029]) (by norm_num [cell13029])
      exact ⟨E.1,E.2.trans (by norm_num [cell13029])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13029

/-! Source-cell containment and simple scalar guards at 13029. -/
namespace BstLean.Part269.N13029
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13029)
open BstLean.Part268 (cell13029)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13029 ⟨10,by decide⟩).lower ∧ (cell13029 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13029 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13029 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13029 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13029 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13029 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13029,cell13029,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13029 ⟨11,by decide⟩).lower ∧ (cell13029 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13029 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13029 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13029 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13029 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13029 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13029,cell13029,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13029 ⟨12,by decide⟩).lower ∧ (cell13029 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13029 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13029 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13029 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13029 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13029 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13029,cell13029,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13029 ⟨13,by decide⟩).lower ∧ (cell13029 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13029 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13029 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13029 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13029 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13029 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13029,cell13029,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13029 ⟨14,by decide⟩).lower ∧ (cell13029 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13029 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13029 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13029 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13029 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13029 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13029,cell13029,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13029 ⟨15,by decide⟩).lower ∧ (cell13029 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13029 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13029 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13029 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13029 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13029 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13029,cell13029,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13029 ⟨16,by decide⟩).lower ∧ (cell13029 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13029 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13029 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13029 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13029 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13029 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13029,cell13029,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13029 ⟨17,by decide⟩).lower ∧ (cell13029 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13029 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13029 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13029 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13029 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13029 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13029,cell13029,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13029 ⟨18,by decide⟩).lower ∧ (cell13029 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13029 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13029 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13029 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13029 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13029 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13029,cell13029,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13029 ⟨19,by decide⟩).lower ∧ (cell13029 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13029 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13029 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13029 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13029 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13029 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13029,cell13029,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13029 ⟨20,by decide⟩).lower ∧ (cell13029 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13029 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13029 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13029 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13029 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13029 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13029,cell13029,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13029 ⟨21,by decide⟩).lower ∧ (cell13029 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13029 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13029 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13029 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13029 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13029 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13029,cell13029,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13029 ⟨22,by decide⟩).lower ∧ (cell13029 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13029 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13029 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13029 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13029 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13029 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13029,cell13029,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13029 ⟨23,by decide⟩).lower ∧ (cell13029 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13029 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13029 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13029 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13029 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13029 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13029,cell13029,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13029 ⟨24,by decide⟩).lower ∧ (cell13029 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13029 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13029 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13029 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13029 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13029 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13029,cell13029,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13029 ⟨25,by decide⟩).lower ∧ (cell13029 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13029 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13029 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13029 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13029 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13029 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13029,cell13029,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13029 ⟨26,by decide⟩).lower ∧ (cell13029 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13029 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13029 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13029 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13029 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13029 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13029,cell13029,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13029 ⟨27,by decide⟩).lower ∧ (cell13029 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13029 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13029 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13029 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13029 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13029 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13029,cell13029,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13029 ⟨28,by decide⟩).lower ∧ (cell13029 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13029 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13029 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13029 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13029 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13029 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13029,cell13029,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13029 ⟨29,by decide⟩).lower ∧ (cell13029 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13029 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13029 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13029 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13029 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13029 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13029,cell13029,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13029 ⟨30,by decide⟩).lower ∧ (cell13029 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13029 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13029 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13029 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13029 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13029 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13029,cell13029,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13029 ⟨31,by decide⟩).lower ∧ (cell13029 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13029 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13029 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13029 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13029 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13029 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13029,cell13029,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13029 ⟨32,by decide⟩).lower ∧ (cell13029 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13029 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13029 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13029 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13029 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13029 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13029,cell13029,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13029 ⟨33,by decide⟩).lower ∧ (cell13029 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13029 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13029 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13029 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13029 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13029 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13029,cell13029,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13029 ⟨34,by decide⟩).lower ∧ (cell13029 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13029 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13029 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13029 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13029 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13029 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13029,cell13029,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13029 ⟨35,by decide⟩).lower ∧ (cell13029 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13029 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13029 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13029 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13029 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13029 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13029,cell13029,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13029 ⟨36,by decide⟩).lower ∧ (cell13029 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13029 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13029 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13029 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13029 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13029 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13029,cell13029,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13029 ⟨37,by decide⟩).lower ∧ (cell13029 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13029 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13029 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13029 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13029 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13029 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13029,cell13029,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13029 ⟨38,by decide⟩).lower ∧ (cell13029 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13029 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13029 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13029 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13029 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13029 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13029,cell13029,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13029 ⟨39,by decide⟩).lower ∧ (cell13029 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13029 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13029 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13029 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13029 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13029 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13029,cell13029,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13029 ⟨40,by decide⟩).lower ∧ (cell13029 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13029 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13029 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13029 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13029 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13029 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13029,cell13029,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13029 ⟨41,by decide⟩).lower ∧ (cell13029 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13029 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13029 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13029 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13029 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13029 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13029,cell13029,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13029 ⟨42,by decide⟩).lower ∧ (cell13029 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13029 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13029 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13029 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13029 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13029 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13029,cell13029,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13029 ⟨43,by decide⟩).lower ∧ (cell13029 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13029 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13029 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13029 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13029 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13029 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13029,cell13029,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13029 ⟨44,by decide⟩).lower ∧ (cell13029 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13029 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13029 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13029 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13029 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13029 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13029,cell13029,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13029 ⟨45,by decide⟩).lower ∧ (cell13029 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13029 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13029 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13029 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13029 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13029 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13029,cell13029,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13029 ⟨46,by decide⟩).lower ∧ (cell13029 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13029 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13029 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13029 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13029 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13029 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13029,cell13029,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13029 ⟨47,by decide⟩).lower ∧ (cell13029 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13029 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13029 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13029 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13029 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13029 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13029,cell13029,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13029 ⟨48,by decide⟩).lower ∧ (cell13029 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13029 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13029 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13029 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13029 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13029 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13029,cell13029,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13029 ⟨49,by decide⟩).lower ∧ (cell13029 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13029 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13029 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13029 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13029 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13029 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13029,cell13029,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13029 ⟨50,by decide⟩).lower ∧ (cell13029 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13029 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13029 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13029 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13029 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13029 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13029,cell13029,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13029 ⟨51,by decide⟩).lower ∧ (cell13029 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13029 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13029 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13029 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13029 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13029 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13029,cell13029,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13029 ⟨52,by decide⟩).lower ∧ (cell13029 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13029 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13029 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13029 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13029 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13029 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13029,cell13029,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13029 i).lower ∧
    (cell13029 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13029 i).upper ≤ (0.532 : ℝ) ∧
    (cell13029 i).centre ≤ (0.1 : ℝ) ∧ (cell13029 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13029 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13029 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13029

/-! The local source numeric instances at 13029 have no network premises. -/
namespace BstLean.Part269.N13029
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13029)
open BstLean.Part268 (cell13029)

noncomputable def sourceNumerics13029 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13029 (cell13029 i)
      scalarRow13029.M scalarRow13029.H scalarRow13029.xi := by
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
    energy_allowance := scalarRow13029.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13029]
    centre_nonneg := (scalarRow13029.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D27.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13029])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13029
/-! Actual 13030 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13030
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13030 ≤ (1.035348894982 : ℝ) := by
  have hr : (114.149025401008 : ℝ) ≤ √(13030 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.149025401008 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13030 13030 (11 / 1000) ≤
    (0.008374026258 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13030) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.149025401008 : ℝ) ≤ √(13030 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13030)
  have hdiv : K / √(13030 : ℝ) ≤ K / 114.149025401008 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.149025401008 ≤ (0.008374026258 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13030.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13030 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13030 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13030 := gPlus_lower 13030
end BstLean.Part269.N13030

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13030
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035348894981 : ℝ) ≤ wn 13030 := by
  have hn : √(13030 : ℝ) ≤ 114.149025401009 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13030 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.149025401009 ≤ 2 / √(13030 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000245392587 : ℝ) ≤ rhoBar 13030 BstLean.Part154.csC ∧
    rhoBar 13030 BstLean.Part154.csC ≤ 0.000245392967 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035348894981 : ℝ) / (1.295212 * 13030) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035348894982 : ℝ) / (1.29521 * 13030) := by gcongr
      _ ≤ (0.000245392967 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13030 BstLean.Part154.csC) ≤ 0.000981632086 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13030 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13030 BstLean.Part154.csC) (piBar (rhoBar 13030 BstLean.Part154.csC)) ≤ 0.000187432579 ∧
    cc1 (rhoBar 13030 BstLean.Part154.csC) (piBar (rhoBar 13030 BstLean.Part154.csC)) ≤ 0.000119264641 ∧
    cc2 (rhoBar 13030 BstLean.Part154.csC) ≤ 0.000069234094 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13030 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13030 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13030 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13030 BstLean.Part154.csC * nuR (rhoBar 13030 BstLean.Part154.csC)) ≤ 0.000490800989 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000245392967 : ℝ) * 0.000981632086 := by gcongr
      _ ≤ (0.000490800989 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13030 BstLean.Part154.csC) * nuR (rhoBar 13030 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000981632086 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13030 BstLean.Part154.csC) * rhoBar 13030 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000245392967 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000245392967 / 2 + 0.399 * 0.000981632086 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000187432579 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000490800989 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119264641 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000245392967 / 1.414213562 := by gcongr
      _ ≤ (0.000069234094 : ℝ) := by norm_num

end BstLean.Part269.N13030

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13030
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13030 BstLean.Part154.csC) (piBar (rhoBar 13030 BstLean.Part154.csC)) ≤ 1.51714E-7 := by
  have hr0 : 0 ≤ rhoBar 13030 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13030 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13030 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13030 BstLean.Part154.csC) (piBar (rhoBar 13030 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13030 BstLean.Part154.csC) (piBar (rhoBar 13030 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13030 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000187432579 : ℝ) ^ 2 + 0.000119264641 ^ 2 + 3 * 0.000069234094 ^ 2 +
        2 * 0.797885 * 0.000187432579 * 0.000119264641 + 2 * 0.000187432579 * 0.000069234094 +
        4 * 0.797885 * 0.000119264641 * 0.000069234094 := by gcongr
    _ ≤ (1.51714E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13030 BstLean.Part154.csC Θ ≤ 0.002560418376 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13030 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13030 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13030 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13030 BstLean.Part154.csC) (piBar (rhoBar 13030 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13030 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035348894982 * 1.51714E-7 / (0.000245392587 : ℝ) := by gcongr
    _ ≤ 0.002560418376 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13030 BstLean.Part154.csC Θ ≤ 0.002839659092 + 0.000646977297 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13030 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13030 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13030 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035348894982 : ℝ) * ((2 * Θ * 0.000245392967 +
        (6863 / 10000) * 0.000245392967 * 13030 * 0.000981632086) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002839659092 + 0.000646977297 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13030 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13030 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13030 0.011 Θ ∧ gammaRatio 13030 0.011 Θ ≤ 0.000084359757 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13030 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035348894982 : ℝ) * 0.525 / ((1 - 0.011) * 13030) := by gcongr
      _ ≤ (0.000084359757 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13030 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13030 0.011 Θ) :=
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
    badAllowance 13030 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000383431726 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13030 BstLean.Part154.csC) 1.22 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 2 (rhoBar 13030 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13030 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13030 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13030 0.011 Θ) 1.12 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 1 (gammaRatio 13030 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13030 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13030 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13030 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13030 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035348894982 : ℝ) * 13030 *
        (1.3781E-8 / 1.1045361 + 1.6832E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000383431726 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13030 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003223090818 + 0.003207395673 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13030

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13030
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13030 BstLean.Part154.csC) (piBar (rhoBar 13030 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13030 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13030 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13030 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13030 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13030 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13030 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13030 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13030 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13030 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13030 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13030 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13030 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13030 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13030 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051808276807 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13030) ≤ 0.010462091787 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13030 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035348894982)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010462091787 + 2 * 0.737676 / 13030) := by gcongr
    _ ≤ (0.051808276807 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13030 12 ≤ 0.0015 := by
  exact BstLean.Part269.S27.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13030

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13030
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560518113914 : ℝ) ≤ plow 13030 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13030) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052413573547)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001344219648) : eMP 13030 0.011 xi bn ≤ 0.001157683421 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13030 : ℝ) * (1 - 0.011))) ≤ 0.000572452856 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001344219648 / (13030 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000572452856 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000572452856 : ℝ) + 3.141593 * 0.052413573547 / (13030 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001157683421 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052413573547)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001344219648) : PiBarMP 13030 12 0.011 xi bn ≤ 0.159175635029 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13030 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036663601133 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.519469695731 : ℝ) ≤ √((13030 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.149025401008 : ℝ) ≤ √(13030 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13030) ≤ 0.122054552931 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036663601133 + 0.052413573547 * 1.772454 / (2 * (113.519469695731 : ℝ))) * (1 + 0.001157683421) +
        8 / (13030 * 114.149025401008) + 0.122054552931 := by gcongr
    _ ≤ (0.159175635029 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052413573547)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001344219648) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280748385891) :
    parallelOracle 13030 0.011 xi bn cd ≤ 0.160140803417 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13030 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13030 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560518113914 : ℝ) ≤ plow 13030 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.149025401008 : ℝ) ≤ √(13030 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280748385891 : ℝ) / (2 * 0.560518113914 * 114.149025401008)) * 0.159175635029 +
        0.280748385891 ^ 2 / (2 * 0.560518113914 * 114.149025401008) := by gcongr
    _ ≤ (0.160140803417 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052413573547) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001344219648)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280748385891) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13030 13030 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560518113914 : ℝ) ≤ plow 13030 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.149025401008 : ℝ) ≤ √(13030 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13030 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13030 Θ 1.22 ≤ 0.011617273957 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.149025401008 := by gcongr <;> linarith
      _ ≤ (0.011617273957 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13030 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13030 13030 0.011 ≤ 0.008374026258 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13030 13030 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13030 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13030 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13030 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13030 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160140803417 + 0.011617273957 + (0.008374026258 : ℝ) *
        (1 + 2 * (0.280748385891 + 0.011617273957) / (0.560518113914 * 114.149025401008))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13030]

end BstLean.Part269.N13030

/-! The original eight local profiles supply actual 13030 moment certificates. -/
namespace BstLean.Part269.N13030
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13030 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13030 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13030 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052413573547 ∧
    0 ≤ bN 13030 BstLean.Part154.csC (groupTheta g) ∧ bN 13030 BstLean.Part154.csC (groupTheta g) ≤ 0.001344219648 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13030 13030 0.011
      (momentAllowance 13030 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13030 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13030 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13030 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13030 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13030 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228940109084 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13030 0.011
      (momentAllowance 13030 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13030 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13030
/-! The actual computed-centre upper energy formula at 13030. -/
namespace BstLean.Part269.N13030
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13030

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13030
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13030)
open BstLean.Part268 (cell13030)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084581916480
  | 2 => 0.085509565627
  | 3 => 0.086433269068
  | 4 => 0.087353954851
  | 5 => 0.088272759810
  | 6 => 0.089191062352
  | 7 => 0.090110518656
  | 8 => 0.091033102401
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13030 13030 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13030 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003224237287 + 0.003208677626 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S27.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13030

/-! Actual upper energy certificates on all 43 source endpoints at 13030. -/
namespace BstLean.Part269.N13030
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13030)
open BstLean.Part268 (cell13030)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13030 (gMinus 13030) (1 - (cell13030 i).lower) ≤ 1 ∧
    energyUpper 13030 (gMinus 13030) (BstLean.Part211.gPlus 13030)
      (finiteEnergy 13030 13030 0.011) (1 - (cell13030 i).lower) ≤
      (cell13030 i).energy := by
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
      have E := BstLean.Part269.S27.uniformEnergy10 (n := 13030) (by norm_num)
        (q := 1 - (cell13030 ⟨10,by decide⟩).lower)
        (by norm_num [cell13030]) (by norm_num [cell13030])
      exact ⟨E.1,E.2.trans (by norm_num [cell13030])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy11 (n := 13030) (by norm_num)
        (q := 1 - (cell13030 ⟨11,by decide⟩).lower)
        (by norm_num [cell13030]) (by norm_num [cell13030])
      exact ⟨E.1,E.2.trans (by norm_num [cell13030])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy12 (n := 13030) (by norm_num)
        (q := 1 - (cell13030 ⟨12,by decide⟩).lower)
        (by norm_num [cell13030]) (by norm_num [cell13030])
      exact ⟨E.1,E.2.trans (by norm_num [cell13030])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy13 (n := 13030) (by norm_num)
        (q := 1 - (cell13030 ⟨13,by decide⟩).lower)
        (by norm_num [cell13030]) (by norm_num [cell13030])
      exact ⟨E.1,E.2.trans (by norm_num [cell13030])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy14 (n := 13030) (by norm_num)
        (q := 1 - (cell13030 ⟨14,by decide⟩).lower)
        (by norm_num [cell13030]) (by norm_num [cell13030])
      exact ⟨E.1,E.2.trans (by norm_num [cell13030])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy15 (n := 13030) (by norm_num)
        (q := 1 - (cell13030 ⟨15,by decide⟩).lower)
        (by norm_num [cell13030]) (by norm_num [cell13030])
      exact ⟨E.1,E.2.trans (by norm_num [cell13030])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy16 (n := 13030) (by norm_num)
        (q := 1 - (cell13030 ⟨16,by decide⟩).lower)
        (by norm_num [cell13030]) (by norm_num [cell13030])
      exact ⟨E.1,E.2.trans (by norm_num [cell13030])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy17 (n := 13030) (by norm_num)
        (q := 1 - (cell13030 ⟨17,by decide⟩).lower)
        (by norm_num [cell13030]) (by norm_num [cell13030])
      exact ⟨E.1,E.2.trans (by norm_num [cell13030])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy18 (n := 13030) (by norm_num)
        (q := 1 - (cell13030 ⟨18,by decide⟩).lower)
        (by norm_num [cell13030]) (by norm_num [cell13030])
      exact ⟨E.1,E.2.trans (by norm_num [cell13030])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy19 (n := 13030) (by norm_num)
        (q := 1 - (cell13030 ⟨19,by decide⟩).lower)
        (by norm_num [cell13030]) (by norm_num [cell13030])
      exact ⟨E.1,E.2.trans (by norm_num [cell13030])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy20 (n := 13030) (by norm_num)
        (q := 1 - (cell13030 ⟨20,by decide⟩).lower)
        (by norm_num [cell13030]) (by norm_num [cell13030])
      exact ⟨E.1,E.2.trans (by norm_num [cell13030])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy21 (n := 13030) (by norm_num)
        (q := 1 - (cell13030 ⟨21,by decide⟩).lower)
        (by norm_num [cell13030]) (by norm_num [cell13030])
      exact ⟨E.1,E.2.trans (by norm_num [cell13030])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy22 (n := 13030) (by norm_num)
        (q := 1 - (cell13030 ⟨22,by decide⟩).lower)
        (by norm_num [cell13030]) (by norm_num [cell13030])
      exact ⟨E.1,E.2.trans (by norm_num [cell13030])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy23 (n := 13030) (by norm_num)
        (q := 1 - (cell13030 ⟨23,by decide⟩).lower)
        (by norm_num [cell13030]) (by norm_num [cell13030])
      exact ⟨E.1,E.2.trans (by norm_num [cell13030])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy24 (n := 13030) (by norm_num)
        (q := 1 - (cell13030 ⟨24,by decide⟩).lower)
        (by norm_num [cell13030]) (by norm_num [cell13030])
      exact ⟨E.1,E.2.trans (by norm_num [cell13030])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy25 (n := 13030) (by norm_num)
        (q := 1 - (cell13030 ⟨25,by decide⟩).lower)
        (by norm_num [cell13030]) (by norm_num [cell13030])
      exact ⟨E.1,E.2.trans (by norm_num [cell13030])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy26 (n := 13030) (by norm_num)
        (q := 1 - (cell13030 ⟨26,by decide⟩).lower)
        (by norm_num [cell13030]) (by norm_num [cell13030])
      exact ⟨E.1,E.2.trans (by norm_num [cell13030])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy27 (n := 13030) (by norm_num)
        (q := 1 - (cell13030 ⟨27,by decide⟩).lower)
        (by norm_num [cell13030]) (by norm_num [cell13030])
      exact ⟨E.1,E.2.trans (by norm_num [cell13030])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy28 (n := 13030) (by norm_num)
        (q := 1 - (cell13030 ⟨28,by decide⟩).lower)
        (by norm_num [cell13030]) (by norm_num [cell13030])
      exact ⟨E.1,E.2.trans (by norm_num [cell13030])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy29 (n := 13030) (by norm_num)
        (q := 1 - (cell13030 ⟨29,by decide⟩).lower)
        (by norm_num [cell13030]) (by norm_num [cell13030])
      exact ⟨E.1,E.2.trans (by norm_num [cell13030])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy30 (n := 13030) (by norm_num)
        (q := 1 - (cell13030 ⟨30,by decide⟩).lower)
        (by norm_num [cell13030]) (by norm_num [cell13030])
      exact ⟨E.1,E.2.trans (by norm_num [cell13030])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy31 (n := 13030) (by norm_num)
        (q := 1 - (cell13030 ⟨31,by decide⟩).lower)
        (by norm_num [cell13030]) (by norm_num [cell13030])
      exact ⟨E.1,E.2.trans (by norm_num [cell13030])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy32 (n := 13030) (by norm_num)
        (q := 1 - (cell13030 ⟨32,by decide⟩).lower)
        (by norm_num [cell13030]) (by norm_num [cell13030])
      exact ⟨E.1,E.2.trans (by norm_num [cell13030])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy33 (n := 13030) (by norm_num)
        (q := 1 - (cell13030 ⟨33,by decide⟩).lower)
        (by norm_num [cell13030]) (by norm_num [cell13030])
      exact ⟨E.1,E.2.trans (by norm_num [cell13030])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy34 (n := 13030) (by norm_num)
        (q := 1 - (cell13030 ⟨34,by decide⟩).lower)
        (by norm_num [cell13030]) (by norm_num [cell13030])
      exact ⟨E.1,E.2.trans (by norm_num [cell13030])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy35 (n := 13030) (by norm_num)
        (q := 1 - (cell13030 ⟨35,by decide⟩).lower)
        (by norm_num [cell13030]) (by norm_num [cell13030])
      exact ⟨E.1,E.2.trans (by norm_num [cell13030])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy36 (n := 13030) (by norm_num)
        (q := 1 - (cell13030 ⟨36,by decide⟩).lower)
        (by norm_num [cell13030]) (by norm_num [cell13030])
      exact ⟨E.1,E.2.trans (by norm_num [cell13030])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy37 (n := 13030) (by norm_num)
        (q := 1 - (cell13030 ⟨37,by decide⟩).lower)
        (by norm_num [cell13030]) (by norm_num [cell13030])
      exact ⟨E.1,E.2.trans (by norm_num [cell13030])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy38 (n := 13030) (by norm_num)
        (q := 1 - (cell13030 ⟨38,by decide⟩).lower)
        (by norm_num [cell13030]) (by norm_num [cell13030])
      exact ⟨E.1,E.2.trans (by norm_num [cell13030])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy39 (n := 13030) (by norm_num)
        (q := 1 - (cell13030 ⟨39,by decide⟩).lower)
        (by norm_num [cell13030]) (by norm_num [cell13030])
      exact ⟨E.1,E.2.trans (by norm_num [cell13030])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy40 (n := 13030) (by norm_num)
        (q := 1 - (cell13030 ⟨40,by decide⟩).lower)
        (by norm_num [cell13030]) (by norm_num [cell13030])
      exact ⟨E.1,E.2.trans (by norm_num [cell13030])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy41 (n := 13030) (by norm_num)
        (q := 1 - (cell13030 ⟨41,by decide⟩).lower)
        (by norm_num [cell13030]) (by norm_num [cell13030])
      exact ⟨E.1,E.2.trans (by norm_num [cell13030])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy42 (n := 13030) (by norm_num)
        (q := 1 - (cell13030 ⟨42,by decide⟩).lower)
        (by norm_num [cell13030]) (by norm_num [cell13030])
      exact ⟨E.1,E.2.trans (by norm_num [cell13030])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy43 (n := 13030) (by norm_num)
        (q := 1 - (cell13030 ⟨43,by decide⟩).lower)
        (by norm_num [cell13030]) (by norm_num [cell13030])
      exact ⟨E.1,E.2.trans (by norm_num [cell13030])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy44 (n := 13030) (by norm_num)
        (q := 1 - (cell13030 ⟨44,by decide⟩).lower)
        (by norm_num [cell13030]) (by norm_num [cell13030])
      exact ⟨E.1,E.2.trans (by norm_num [cell13030])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy45 (n := 13030) (by norm_num)
        (q := 1 - (cell13030 ⟨45,by decide⟩).lower)
        (by norm_num [cell13030]) (by norm_num [cell13030])
      exact ⟨E.1,E.2.trans (by norm_num [cell13030])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy46 (n := 13030) (by norm_num)
        (q := 1 - (cell13030 ⟨46,by decide⟩).lower)
        (by norm_num [cell13030]) (by norm_num [cell13030])
      exact ⟨E.1,E.2.trans (by norm_num [cell13030])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy47 (n := 13030) (by norm_num)
        (q := 1 - (cell13030 ⟨47,by decide⟩).lower)
        (by norm_num [cell13030]) (by norm_num [cell13030])
      exact ⟨E.1,E.2.trans (by norm_num [cell13030])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy48 (n := 13030) (by norm_num)
        (q := 1 - (cell13030 ⟨48,by decide⟩).lower)
        (by norm_num [cell13030]) (by norm_num [cell13030])
      exact ⟨E.1,E.2.trans (by norm_num [cell13030])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy49 (n := 13030) (by norm_num)
        (q := 1 - (cell13030 ⟨49,by decide⟩).lower)
        (by norm_num [cell13030]) (by norm_num [cell13030])
      exact ⟨E.1,E.2.trans (by norm_num [cell13030])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy50 (n := 13030) (by norm_num)
        (q := 1 - (cell13030 ⟨50,by decide⟩).lower)
        (by norm_num [cell13030]) (by norm_num [cell13030])
      exact ⟨E.1,E.2.trans (by norm_num [cell13030])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy51 (n := 13030) (by norm_num)
        (q := 1 - (cell13030 ⟨51,by decide⟩).lower)
        (by norm_num [cell13030]) (by norm_num [cell13030])
      exact ⟨E.1,E.2.trans (by norm_num [cell13030])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy52 (n := 13030) (by norm_num)
        (q := 1 - (cell13030 ⟨52,by decide⟩).lower)
        (by norm_num [cell13030]) (by norm_num [cell13030])
      exact ⟨E.1,E.2.trans (by norm_num [cell13030])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13030

/-! Source-cell containment and simple scalar guards at 13030. -/
namespace BstLean.Part269.N13030
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13030)
open BstLean.Part268 (cell13030)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13030 ⟨10,by decide⟩).lower ∧ (cell13030 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13030 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13030 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13030 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13030 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13030 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13030,cell13030,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13030 ⟨11,by decide⟩).lower ∧ (cell13030 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13030 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13030 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13030 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13030 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13030 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13030,cell13030,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13030 ⟨12,by decide⟩).lower ∧ (cell13030 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13030 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13030 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13030 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13030 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13030 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13030,cell13030,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13030 ⟨13,by decide⟩).lower ∧ (cell13030 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13030 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13030 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13030 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13030 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13030 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13030,cell13030,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13030 ⟨14,by decide⟩).lower ∧ (cell13030 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13030 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13030 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13030 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13030 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13030 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13030,cell13030,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13030 ⟨15,by decide⟩).lower ∧ (cell13030 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13030 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13030 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13030 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13030 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13030 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13030,cell13030,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13030 ⟨16,by decide⟩).lower ∧ (cell13030 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13030 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13030 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13030 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13030 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13030 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13030,cell13030,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13030 ⟨17,by decide⟩).lower ∧ (cell13030 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13030 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13030 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13030 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13030 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13030 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13030,cell13030,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13030 ⟨18,by decide⟩).lower ∧ (cell13030 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13030 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13030 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13030 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13030 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13030 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13030,cell13030,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13030 ⟨19,by decide⟩).lower ∧ (cell13030 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13030 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13030 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13030 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13030 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13030 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13030,cell13030,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13030 ⟨20,by decide⟩).lower ∧ (cell13030 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13030 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13030 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13030 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13030 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13030 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13030,cell13030,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13030 ⟨21,by decide⟩).lower ∧ (cell13030 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13030 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13030 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13030 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13030 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13030 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13030,cell13030,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13030 ⟨22,by decide⟩).lower ∧ (cell13030 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13030 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13030 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13030 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13030 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13030 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13030,cell13030,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13030 ⟨23,by decide⟩).lower ∧ (cell13030 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13030 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13030 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13030 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13030 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13030 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13030,cell13030,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13030 ⟨24,by decide⟩).lower ∧ (cell13030 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13030 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13030 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13030 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13030 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13030 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13030,cell13030,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13030 ⟨25,by decide⟩).lower ∧ (cell13030 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13030 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13030 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13030 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13030 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13030 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13030,cell13030,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13030 ⟨26,by decide⟩).lower ∧ (cell13030 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13030 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13030 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13030 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13030 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13030 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13030,cell13030,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13030 ⟨27,by decide⟩).lower ∧ (cell13030 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13030 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13030 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13030 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13030 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13030 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13030,cell13030,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13030 ⟨28,by decide⟩).lower ∧ (cell13030 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13030 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13030 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13030 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13030 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13030 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13030,cell13030,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13030 ⟨29,by decide⟩).lower ∧ (cell13030 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13030 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13030 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13030 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13030 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13030 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13030,cell13030,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13030 ⟨30,by decide⟩).lower ∧ (cell13030 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13030 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13030 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13030 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13030 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13030 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13030,cell13030,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13030 ⟨31,by decide⟩).lower ∧ (cell13030 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13030 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13030 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13030 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13030 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13030 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13030,cell13030,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13030 ⟨32,by decide⟩).lower ∧ (cell13030 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13030 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13030 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13030 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13030 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13030 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13030,cell13030,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13030 ⟨33,by decide⟩).lower ∧ (cell13030 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13030 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13030 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13030 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13030 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13030 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13030,cell13030,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13030 ⟨34,by decide⟩).lower ∧ (cell13030 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13030 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13030 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13030 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13030 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13030 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13030,cell13030,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13030 ⟨35,by decide⟩).lower ∧ (cell13030 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13030 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13030 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13030 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13030 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13030 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13030,cell13030,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13030 ⟨36,by decide⟩).lower ∧ (cell13030 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13030 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13030 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13030 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13030 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13030 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13030,cell13030,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13030 ⟨37,by decide⟩).lower ∧ (cell13030 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13030 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13030 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13030 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13030 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13030 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13030,cell13030,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13030 ⟨38,by decide⟩).lower ∧ (cell13030 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13030 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13030 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13030 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13030 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13030 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13030,cell13030,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13030 ⟨39,by decide⟩).lower ∧ (cell13030 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13030 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13030 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13030 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13030 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13030 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13030,cell13030,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13030 ⟨40,by decide⟩).lower ∧ (cell13030 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13030 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13030 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13030 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13030 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13030 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13030,cell13030,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13030 ⟨41,by decide⟩).lower ∧ (cell13030 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13030 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13030 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13030 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13030 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13030 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13030,cell13030,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13030 ⟨42,by decide⟩).lower ∧ (cell13030 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13030 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13030 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13030 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13030 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13030 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13030,cell13030,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13030 ⟨43,by decide⟩).lower ∧ (cell13030 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13030 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13030 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13030 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13030 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13030 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13030,cell13030,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13030 ⟨44,by decide⟩).lower ∧ (cell13030 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13030 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13030 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13030 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13030 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13030 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13030,cell13030,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13030 ⟨45,by decide⟩).lower ∧ (cell13030 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13030 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13030 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13030 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13030 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13030 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13030,cell13030,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13030 ⟨46,by decide⟩).lower ∧ (cell13030 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13030 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13030 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13030 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13030 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13030 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13030,cell13030,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13030 ⟨47,by decide⟩).lower ∧ (cell13030 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13030 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13030 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13030 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13030 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13030 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13030,cell13030,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13030 ⟨48,by decide⟩).lower ∧ (cell13030 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13030 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13030 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13030 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13030 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13030 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13030,cell13030,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13030 ⟨49,by decide⟩).lower ∧ (cell13030 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13030 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13030 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13030 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13030 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13030 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13030,cell13030,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13030 ⟨50,by decide⟩).lower ∧ (cell13030 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13030 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13030 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13030 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13030 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13030 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13030,cell13030,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13030 ⟨51,by decide⟩).lower ∧ (cell13030 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13030 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13030 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13030 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13030 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13030 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13030,cell13030,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13030 ⟨52,by decide⟩).lower ∧ (cell13030 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13030 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13030 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13030 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13030 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13030 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13030,cell13030,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13030 i).lower ∧
    (cell13030 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13030 i).upper ≤ (0.532 : ℝ) ∧
    (cell13030 i).centre ≤ (0.1 : ℝ) ∧ (cell13030 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13030 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13030 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13030

/-! The local source numeric instances at 13030 have no network premises. -/
namespace BstLean.Part269.N13030
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13030)
open BstLean.Part268 (cell13030)

noncomputable def sourceNumerics13030 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13030 (cell13030 i)
      scalarRow13030.M scalarRow13030.H scalarRow13030.xi := by
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
    energy_allowance := scalarRow13030.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13030]
    centre_nonneg := (scalarRow13030.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D27.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13030])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13030
/-! Actual 13031 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13031
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13031 ≤ (1.035347526838 : ℝ) := by
  have hr : (114.153405555857 : ℝ) ≤ √(13031 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.153405555857 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13031 13031 (11 / 1000) ≤
    (0.008373704938 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13031) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.153405555857 : ℝ) ≤ √(13031 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13031)
  have hdiv : K / √(13031 : ℝ) ≤ K / 114.153405555857 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.153405555857 ≤ (0.008373704938 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13031.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13031 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13031 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13031 := gPlus_lower 13031
end BstLean.Part269.N13031

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13031
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035347526837 : ℝ) ≤ wn 13031 := by
  have hn : √(13031 : ℝ) ≤ 114.153405555858 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13031 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.153405555858 ≤ 2 / √(13031 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000245373432 : ℝ) ≤ rhoBar 13031 BstLean.Part154.csC ∧
    rhoBar 13031 BstLean.Part154.csC ≤ 0.000245373811 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035347526837 : ℝ) / (1.295212 * 13031) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035347526838 : ℝ) / (1.29521 * 13031) := by gcongr
      _ ≤ (0.000245373811 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13031 BstLean.Part154.csC) ≤ 0.000981555453 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13031 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13031 BstLean.Part154.csC) (piBar (rhoBar 13031 BstLean.Part154.csC)) ≤ 0.000187417947 ∧
    cc1 (rhoBar 13031 BstLean.Part154.csC) (piBar (rhoBar 13031 BstLean.Part154.csC)) ≤ 0.000119255331 ∧
    cc2 (rhoBar 13031 BstLean.Part154.csC) ≤ 0.000069228689 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13031 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13031 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13031 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13031 BstLean.Part154.csC * nuR (rhoBar 13031 BstLean.Part154.csC)) ≤ 0.000490762675 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000245373811 : ℝ) * 0.000981555453 := by gcongr
      _ ≤ (0.000490762675 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13031 BstLean.Part154.csC) * nuR (rhoBar 13031 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000981555453 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13031 BstLean.Part154.csC) * rhoBar 13031 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000245373811 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000245373811 / 2 + 0.399 * 0.000981555453 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000187417947 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000490762675 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119255331 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000245373811 / 1.414213562 := by gcongr
      _ ≤ (0.000069228689 : ℝ) := by norm_num

end BstLean.Part269.N13031

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13031
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13031 BstLean.Part154.csC) (piBar (rhoBar 13031 BstLean.Part154.csC)) ≤ 1.51690E-7 := by
  have hr0 : 0 ≤ rhoBar 13031 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13031 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13031 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13031 BstLean.Part154.csC) (piBar (rhoBar 13031 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13031 BstLean.Part154.csC) (piBar (rhoBar 13031 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13031 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000187417947 : ℝ) ^ 2 + 0.000119255331 ^ 2 + 3 * 0.000069228689 ^ 2 +
        2 * 0.797885 * 0.000187417947 * 0.000119255331 + 2 * 0.000187417947 * 0.000069228689 +
        4 * 0.797885 * 0.000119255331 * 0.000069228689 := by gcongr
    _ ≤ (1.51690E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13031 BstLean.Part154.csC Θ ≤ 0.002560209801 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13031 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13031 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13031 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13031 BstLean.Part154.csC) (piBar (rhoBar 13031 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13031 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035347526838 * 1.51690E-7 / (0.000245373432 : ℝ) := by gcongr
    _ ≤ 0.002560209801 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13031 BstLean.Part154.csC Θ ≤ 0.002839429901 + 0.000646925937 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13031 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13031 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13031 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035347526838 : ℝ) * ((2 * Θ * 0.000245373811 +
        (6863 / 10000) * 0.000245373811 * 13031 * 0.000981555453) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002839429901 + 0.000646925937 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13031 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13031 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13031 0.011 Θ ∧ gammaRatio 13031 0.011 Θ ≤ 0.000084353171 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13031 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035347526838 : ℝ) * 0.525 / ((1 - 0.011) * 13031) := by gcongr
      _ ≤ (0.000084353171 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13031 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13031 0.011 Θ) :=
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
    badAllowance 13031 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000383431726 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13031 BstLean.Part154.csC) 1.22 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 2 (rhoBar 13031 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13031 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13031 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13031 0.011 Θ) 1.12 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 1 (gammaRatio 13031 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13031 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13031 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13031 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13031 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035347526838 : ℝ) * 13031 *
        (1.3781E-8 / 1.1045361 + 1.6832E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000383431726 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13031 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003222861627 + 0.003207135738 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13031

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13031
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13031 BstLean.Part154.csC) (piBar (rhoBar 13031 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13031 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13031 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13031 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13031 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13031 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13031 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13031 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13031 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13031 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13031 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13031 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13031 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13031 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13031 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051806267598 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13031) ≤ 0.010461690348 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13031 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035347526838)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010461690348 + 2 * 0.737676 / 13031) := by gcongr
    _ ≤ (0.051806267598 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13031 12 ≤ 0.0015 := by
  exact BstLean.Part269.S27.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13031

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13031
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560518156872 : ℝ) ≤ plow 13031 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13031) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052413207890)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001344110146) : eMP 13031 0.011 xi bn ≤ 0.001157591790 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13031 : ℝ) * (1 - 0.011))) ≤ 0.000572407575 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001344110146 / (13031 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000572407575 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000572407575 : ℝ) + 3.141593 * 0.052413207890 / (13031 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001157591790 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052413207890)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001344110146) : PiBarMP 13031 12 0.011 xi bn ≤ 0.159169434016 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13031 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036662107769 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.523825693111 : ℝ) ≤ √((13031 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.153405555857 : ℝ) ≤ √(13031 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13031) ≤ 0.122049869603 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036662107769 + 0.052413207890 * 1.772454 / (2 * (113.523825693111 : ℝ))) * (1 + 0.001157591790) +
        8 / (13031 * 114.153405555857) + 0.122049869603 := by gcongr
    _ ≤ (0.159169434016 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052413207890)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001344110146) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280745578094) :
    parallelOracle 13031 0.011 xi bn cd ≤ 0.160134535879 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13031 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13031 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560518156872 : ℝ) ≤ plow 13031 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.153405555857 : ℝ) ≤ √(13031 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280745578094 : ℝ) / (2 * 0.560518156872 * 114.153405555857)) * 0.159169434016 +
        0.280745578094 ^ 2 / (2 * 0.560518156872 * 114.153405555857) := by gcongr
    _ ≤ (0.160134535879 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052413207890) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001344110146)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280745578094) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13031 13031 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560518156872 : ℝ) ≤ plow 13031 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.153405555857 : ℝ) ≤ √(13031 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13031 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13031 Θ 1.22 ≤ 0.011616828194 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.153405555857 := by gcongr <;> linarith
      _ ≤ (0.011616828194 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13031 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13031 13031 0.011 ≤ 0.008373704938 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13031 13031 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13031 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13031 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13031 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13031 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160134535879 + 0.011616828194 + (0.008373704938 : ℝ) *
        (1 + 2 * (0.280745578094 + 0.011616828194) / (0.560518156872 * 114.153405555857))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13031]

end BstLean.Part269.N13031

/-! The original eight local profiles supply actual 13031 moment certificates. -/
namespace BstLean.Part269.N13031
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13031 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13031 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13031 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052413207890 ∧
    0 ≤ bN 13031 BstLean.Part154.csC (groupTheta g) ∧ bN 13031 BstLean.Part154.csC (groupTheta g) ≤ 0.001344110146 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13031 13031 0.011
      (momentAllowance 13031 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13031 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13031 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13031 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13031 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13031 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228939310496 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13031 0.011
      (momentAllowance 13031 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13031 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13031
/-! The actual computed-centre upper energy formula at 13031. -/
namespace BstLean.Part269.N13031
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13031

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13031
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13031)
open BstLean.Part268 (cell13031)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084579322153
  | 2 => 0.085506937592
  | 3 => 0.086430602271
  | 4 => 0.087351243049
  | 5 => 0.088269995354
  | 6 => 0.089188235941
  | 7 => 0.090107619059
  | 8 => 0.091030116148
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13031 13031 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13031 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003224237287 + 0.003208677626 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S27.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13031

/-! Actual upper energy certificates on all 43 source endpoints at 13031. -/
namespace BstLean.Part269.N13031
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13031)
open BstLean.Part268 (cell13031)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13031 (gMinus 13031) (1 - (cell13031 i).lower) ≤ 1 ∧
    energyUpper 13031 (gMinus 13031) (BstLean.Part211.gPlus 13031)
      (finiteEnergy 13031 13031 0.011) (1 - (cell13031 i).lower) ≤
      (cell13031 i).energy := by
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
      have E := BstLean.Part269.S27.uniformEnergy10 (n := 13031) (by norm_num)
        (q := 1 - (cell13031 ⟨10,by decide⟩).lower)
        (by norm_num [cell13031]) (by norm_num [cell13031])
      exact ⟨E.1,E.2.trans (by norm_num [cell13031])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy11 (n := 13031) (by norm_num)
        (q := 1 - (cell13031 ⟨11,by decide⟩).lower)
        (by norm_num [cell13031]) (by norm_num [cell13031])
      exact ⟨E.1,E.2.trans (by norm_num [cell13031])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy12 (n := 13031) (by norm_num)
        (q := 1 - (cell13031 ⟨12,by decide⟩).lower)
        (by norm_num [cell13031]) (by norm_num [cell13031])
      exact ⟨E.1,E.2.trans (by norm_num [cell13031])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy13 (n := 13031) (by norm_num)
        (q := 1 - (cell13031 ⟨13,by decide⟩).lower)
        (by norm_num [cell13031]) (by norm_num [cell13031])
      exact ⟨E.1,E.2.trans (by norm_num [cell13031])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy14 (n := 13031) (by norm_num)
        (q := 1 - (cell13031 ⟨14,by decide⟩).lower)
        (by norm_num [cell13031]) (by norm_num [cell13031])
      exact ⟨E.1,E.2.trans (by norm_num [cell13031])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy15 (n := 13031) (by norm_num)
        (q := 1 - (cell13031 ⟨15,by decide⟩).lower)
        (by norm_num [cell13031]) (by norm_num [cell13031])
      exact ⟨E.1,E.2.trans (by norm_num [cell13031])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy16 (n := 13031) (by norm_num)
        (q := 1 - (cell13031 ⟨16,by decide⟩).lower)
        (by norm_num [cell13031]) (by norm_num [cell13031])
      exact ⟨E.1,E.2.trans (by norm_num [cell13031])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy17 (n := 13031) (by norm_num)
        (q := 1 - (cell13031 ⟨17,by decide⟩).lower)
        (by norm_num [cell13031]) (by norm_num [cell13031])
      exact ⟨E.1,E.2.trans (by norm_num [cell13031])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy18 (n := 13031) (by norm_num)
        (q := 1 - (cell13031 ⟨18,by decide⟩).lower)
        (by norm_num [cell13031]) (by norm_num [cell13031])
      exact ⟨E.1,E.2.trans (by norm_num [cell13031])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy19 (n := 13031) (by norm_num)
        (q := 1 - (cell13031 ⟨19,by decide⟩).lower)
        (by norm_num [cell13031]) (by norm_num [cell13031])
      exact ⟨E.1,E.2.trans (by norm_num [cell13031])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy20 (n := 13031) (by norm_num)
        (q := 1 - (cell13031 ⟨20,by decide⟩).lower)
        (by norm_num [cell13031]) (by norm_num [cell13031])
      exact ⟨E.1,E.2.trans (by norm_num [cell13031])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy21 (n := 13031) (by norm_num)
        (q := 1 - (cell13031 ⟨21,by decide⟩).lower)
        (by norm_num [cell13031]) (by norm_num [cell13031])
      exact ⟨E.1,E.2.trans (by norm_num [cell13031])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy22 (n := 13031) (by norm_num)
        (q := 1 - (cell13031 ⟨22,by decide⟩).lower)
        (by norm_num [cell13031]) (by norm_num [cell13031])
      exact ⟨E.1,E.2.trans (by norm_num [cell13031])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy23 (n := 13031) (by norm_num)
        (q := 1 - (cell13031 ⟨23,by decide⟩).lower)
        (by norm_num [cell13031]) (by norm_num [cell13031])
      exact ⟨E.1,E.2.trans (by norm_num [cell13031])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy24 (n := 13031) (by norm_num)
        (q := 1 - (cell13031 ⟨24,by decide⟩).lower)
        (by norm_num [cell13031]) (by norm_num [cell13031])
      exact ⟨E.1,E.2.trans (by norm_num [cell13031])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy25 (n := 13031) (by norm_num)
        (q := 1 - (cell13031 ⟨25,by decide⟩).lower)
        (by norm_num [cell13031]) (by norm_num [cell13031])
      exact ⟨E.1,E.2.trans (by norm_num [cell13031])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy26 (n := 13031) (by norm_num)
        (q := 1 - (cell13031 ⟨26,by decide⟩).lower)
        (by norm_num [cell13031]) (by norm_num [cell13031])
      exact ⟨E.1,E.2.trans (by norm_num [cell13031])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy27 (n := 13031) (by norm_num)
        (q := 1 - (cell13031 ⟨27,by decide⟩).lower)
        (by norm_num [cell13031]) (by norm_num [cell13031])
      exact ⟨E.1,E.2.trans (by norm_num [cell13031])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy28 (n := 13031) (by norm_num)
        (q := 1 - (cell13031 ⟨28,by decide⟩).lower)
        (by norm_num [cell13031]) (by norm_num [cell13031])
      exact ⟨E.1,E.2.trans (by norm_num [cell13031])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy29 (n := 13031) (by norm_num)
        (q := 1 - (cell13031 ⟨29,by decide⟩).lower)
        (by norm_num [cell13031]) (by norm_num [cell13031])
      exact ⟨E.1,E.2.trans (by norm_num [cell13031])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy30 (n := 13031) (by norm_num)
        (q := 1 - (cell13031 ⟨30,by decide⟩).lower)
        (by norm_num [cell13031]) (by norm_num [cell13031])
      exact ⟨E.1,E.2.trans (by norm_num [cell13031])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy31 (n := 13031) (by norm_num)
        (q := 1 - (cell13031 ⟨31,by decide⟩).lower)
        (by norm_num [cell13031]) (by norm_num [cell13031])
      exact ⟨E.1,E.2.trans (by norm_num [cell13031])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy32 (n := 13031) (by norm_num)
        (q := 1 - (cell13031 ⟨32,by decide⟩).lower)
        (by norm_num [cell13031]) (by norm_num [cell13031])
      exact ⟨E.1,E.2.trans (by norm_num [cell13031])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy33 (n := 13031) (by norm_num)
        (q := 1 - (cell13031 ⟨33,by decide⟩).lower)
        (by norm_num [cell13031]) (by norm_num [cell13031])
      exact ⟨E.1,E.2.trans (by norm_num [cell13031])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy34 (n := 13031) (by norm_num)
        (q := 1 - (cell13031 ⟨34,by decide⟩).lower)
        (by norm_num [cell13031]) (by norm_num [cell13031])
      exact ⟨E.1,E.2.trans (by norm_num [cell13031])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy35 (n := 13031) (by norm_num)
        (q := 1 - (cell13031 ⟨35,by decide⟩).lower)
        (by norm_num [cell13031]) (by norm_num [cell13031])
      exact ⟨E.1,E.2.trans (by norm_num [cell13031])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy36 (n := 13031) (by norm_num)
        (q := 1 - (cell13031 ⟨36,by decide⟩).lower)
        (by norm_num [cell13031]) (by norm_num [cell13031])
      exact ⟨E.1,E.2.trans (by norm_num [cell13031])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy37 (n := 13031) (by norm_num)
        (q := 1 - (cell13031 ⟨37,by decide⟩).lower)
        (by norm_num [cell13031]) (by norm_num [cell13031])
      exact ⟨E.1,E.2.trans (by norm_num [cell13031])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy38 (n := 13031) (by norm_num)
        (q := 1 - (cell13031 ⟨38,by decide⟩).lower)
        (by norm_num [cell13031]) (by norm_num [cell13031])
      exact ⟨E.1,E.2.trans (by norm_num [cell13031])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy39 (n := 13031) (by norm_num)
        (q := 1 - (cell13031 ⟨39,by decide⟩).lower)
        (by norm_num [cell13031]) (by norm_num [cell13031])
      exact ⟨E.1,E.2.trans (by norm_num [cell13031])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy40 (n := 13031) (by norm_num)
        (q := 1 - (cell13031 ⟨40,by decide⟩).lower)
        (by norm_num [cell13031]) (by norm_num [cell13031])
      exact ⟨E.1,E.2.trans (by norm_num [cell13031])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy41 (n := 13031) (by norm_num)
        (q := 1 - (cell13031 ⟨41,by decide⟩).lower)
        (by norm_num [cell13031]) (by norm_num [cell13031])
      exact ⟨E.1,E.2.trans (by norm_num [cell13031])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy42 (n := 13031) (by norm_num)
        (q := 1 - (cell13031 ⟨42,by decide⟩).lower)
        (by norm_num [cell13031]) (by norm_num [cell13031])
      exact ⟨E.1,E.2.trans (by norm_num [cell13031])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy43 (n := 13031) (by norm_num)
        (q := 1 - (cell13031 ⟨43,by decide⟩).lower)
        (by norm_num [cell13031]) (by norm_num [cell13031])
      exact ⟨E.1,E.2.trans (by norm_num [cell13031])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy44 (n := 13031) (by norm_num)
        (q := 1 - (cell13031 ⟨44,by decide⟩).lower)
        (by norm_num [cell13031]) (by norm_num [cell13031])
      exact ⟨E.1,E.2.trans (by norm_num [cell13031])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy45 (n := 13031) (by norm_num)
        (q := 1 - (cell13031 ⟨45,by decide⟩).lower)
        (by norm_num [cell13031]) (by norm_num [cell13031])
      exact ⟨E.1,E.2.trans (by norm_num [cell13031])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy46 (n := 13031) (by norm_num)
        (q := 1 - (cell13031 ⟨46,by decide⟩).lower)
        (by norm_num [cell13031]) (by norm_num [cell13031])
      exact ⟨E.1,E.2.trans (by norm_num [cell13031])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy47 (n := 13031) (by norm_num)
        (q := 1 - (cell13031 ⟨47,by decide⟩).lower)
        (by norm_num [cell13031]) (by norm_num [cell13031])
      exact ⟨E.1,E.2.trans (by norm_num [cell13031])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy48 (n := 13031) (by norm_num)
        (q := 1 - (cell13031 ⟨48,by decide⟩).lower)
        (by norm_num [cell13031]) (by norm_num [cell13031])
      exact ⟨E.1,E.2.trans (by norm_num [cell13031])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy49 (n := 13031) (by norm_num)
        (q := 1 - (cell13031 ⟨49,by decide⟩).lower)
        (by norm_num [cell13031]) (by norm_num [cell13031])
      exact ⟨E.1,E.2.trans (by norm_num [cell13031])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy50 (n := 13031) (by norm_num)
        (q := 1 - (cell13031 ⟨50,by decide⟩).lower)
        (by norm_num [cell13031]) (by norm_num [cell13031])
      exact ⟨E.1,E.2.trans (by norm_num [cell13031])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy51 (n := 13031) (by norm_num)
        (q := 1 - (cell13031 ⟨51,by decide⟩).lower)
        (by norm_num [cell13031]) (by norm_num [cell13031])
      exact ⟨E.1,E.2.trans (by norm_num [cell13031])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy52 (n := 13031) (by norm_num)
        (q := 1 - (cell13031 ⟨52,by decide⟩).lower)
        (by norm_num [cell13031]) (by norm_num [cell13031])
      exact ⟨E.1,E.2.trans (by norm_num [cell13031])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13031

/-! Source-cell containment and simple scalar guards at 13031. -/
namespace BstLean.Part269.N13031
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13031)
open BstLean.Part268 (cell13031)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13031 ⟨10,by decide⟩).lower ∧ (cell13031 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13031 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13031 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13031 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13031 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13031 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13031,cell13031,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13031 ⟨11,by decide⟩).lower ∧ (cell13031 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13031 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13031 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13031 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13031 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13031 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13031,cell13031,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13031 ⟨12,by decide⟩).lower ∧ (cell13031 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13031 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13031 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13031 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13031 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13031 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13031,cell13031,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13031 ⟨13,by decide⟩).lower ∧ (cell13031 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13031 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13031 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13031 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13031 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13031 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13031,cell13031,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13031 ⟨14,by decide⟩).lower ∧ (cell13031 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13031 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13031 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13031 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13031 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13031 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13031,cell13031,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13031 ⟨15,by decide⟩).lower ∧ (cell13031 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13031 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13031 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13031 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13031 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13031 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13031,cell13031,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13031 ⟨16,by decide⟩).lower ∧ (cell13031 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13031 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13031 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13031 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13031 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13031 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13031,cell13031,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13031 ⟨17,by decide⟩).lower ∧ (cell13031 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13031 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13031 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13031 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13031 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13031 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13031,cell13031,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13031 ⟨18,by decide⟩).lower ∧ (cell13031 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13031 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13031 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13031 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13031 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13031 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13031,cell13031,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13031 ⟨19,by decide⟩).lower ∧ (cell13031 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13031 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13031 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13031 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13031 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13031 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13031,cell13031,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13031 ⟨20,by decide⟩).lower ∧ (cell13031 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13031 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13031 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13031 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13031 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13031 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13031,cell13031,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13031 ⟨21,by decide⟩).lower ∧ (cell13031 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13031 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13031 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13031 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13031 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13031 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13031,cell13031,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13031 ⟨22,by decide⟩).lower ∧ (cell13031 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13031 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13031 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13031 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13031 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13031 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13031,cell13031,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13031 ⟨23,by decide⟩).lower ∧ (cell13031 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13031 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13031 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13031 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13031 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13031 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13031,cell13031,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13031 ⟨24,by decide⟩).lower ∧ (cell13031 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13031 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13031 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13031 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13031 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13031 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13031,cell13031,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13031 ⟨25,by decide⟩).lower ∧ (cell13031 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13031 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13031 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13031 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13031 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13031 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13031,cell13031,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13031 ⟨26,by decide⟩).lower ∧ (cell13031 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13031 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13031 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13031 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13031 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13031 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13031,cell13031,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13031 ⟨27,by decide⟩).lower ∧ (cell13031 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13031 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13031 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13031 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13031 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13031 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13031,cell13031,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13031 ⟨28,by decide⟩).lower ∧ (cell13031 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13031 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13031 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13031 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13031 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13031 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13031,cell13031,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13031 ⟨29,by decide⟩).lower ∧ (cell13031 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13031 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13031 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13031 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13031 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13031 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13031,cell13031,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13031 ⟨30,by decide⟩).lower ∧ (cell13031 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13031 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13031 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13031 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13031 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13031 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13031,cell13031,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13031 ⟨31,by decide⟩).lower ∧ (cell13031 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13031 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13031 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13031 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13031 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13031 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13031,cell13031,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13031 ⟨32,by decide⟩).lower ∧ (cell13031 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13031 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13031 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13031 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13031 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13031 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13031,cell13031,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13031 ⟨33,by decide⟩).lower ∧ (cell13031 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13031 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13031 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13031 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13031 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13031 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13031,cell13031,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13031 ⟨34,by decide⟩).lower ∧ (cell13031 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13031 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13031 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13031 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13031 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13031 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13031,cell13031,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13031 ⟨35,by decide⟩).lower ∧ (cell13031 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13031 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13031 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13031 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13031 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13031 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13031,cell13031,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13031 ⟨36,by decide⟩).lower ∧ (cell13031 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13031 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13031 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13031 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13031 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13031 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13031,cell13031,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13031 ⟨37,by decide⟩).lower ∧ (cell13031 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13031 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13031 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13031 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13031 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13031 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13031,cell13031,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13031 ⟨38,by decide⟩).lower ∧ (cell13031 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13031 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13031 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13031 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13031 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13031 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13031,cell13031,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13031 ⟨39,by decide⟩).lower ∧ (cell13031 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13031 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13031 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13031 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13031 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13031 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13031,cell13031,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13031 ⟨40,by decide⟩).lower ∧ (cell13031 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13031 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13031 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13031 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13031 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13031 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13031,cell13031,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13031 ⟨41,by decide⟩).lower ∧ (cell13031 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13031 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13031 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13031 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13031 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13031 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13031,cell13031,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13031 ⟨42,by decide⟩).lower ∧ (cell13031 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13031 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13031 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13031 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13031 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13031 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13031,cell13031,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13031 ⟨43,by decide⟩).lower ∧ (cell13031 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13031 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13031 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13031 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13031 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13031 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13031,cell13031,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13031 ⟨44,by decide⟩).lower ∧ (cell13031 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13031 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13031 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13031 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13031 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13031 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13031,cell13031,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13031 ⟨45,by decide⟩).lower ∧ (cell13031 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13031 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13031 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13031 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13031 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13031 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13031,cell13031,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13031 ⟨46,by decide⟩).lower ∧ (cell13031 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13031 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13031 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13031 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13031 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13031 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13031,cell13031,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13031 ⟨47,by decide⟩).lower ∧ (cell13031 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13031 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13031 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13031 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13031 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13031 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13031,cell13031,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13031 ⟨48,by decide⟩).lower ∧ (cell13031 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13031 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13031 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13031 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13031 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13031 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13031,cell13031,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13031 ⟨49,by decide⟩).lower ∧ (cell13031 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13031 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13031 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13031 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13031 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13031 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13031,cell13031,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13031 ⟨50,by decide⟩).lower ∧ (cell13031 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13031 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13031 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13031 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13031 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13031 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13031,cell13031,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13031 ⟨51,by decide⟩).lower ∧ (cell13031 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13031 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13031 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13031 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13031 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13031 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13031,cell13031,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13031 ⟨52,by decide⟩).lower ∧ (cell13031 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13031 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13031 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13031 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13031 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13031 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13031,cell13031,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13031 i).lower ∧
    (cell13031 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13031 i).upper ≤ (0.532 : ℝ) ∧
    (cell13031 i).centre ≤ (0.1 : ℝ) ∧ (cell13031 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13031 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13031 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13031

/-! The local source numeric instances at 13031 have no network premises. -/
namespace BstLean.Part269.N13031
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13031)
open BstLean.Part268 (cell13031)

noncomputable def sourceNumerics13031 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13031 (cell13031 i)
      scalarRow13031.M scalarRow13031.H scalarRow13031.xi := by
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
    energy_allowance := scalarRow13031.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13031]
    centre_nonneg := (scalarRow13031.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D27.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13031])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13031
/-! Actual 13032 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13032
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13032 ≤ (1.035346158853 : ℝ) := by
  have hr : (114.157785542642 : ℝ) ≤ √(13032 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.157785542642 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13032 13032 (11 / 1000) ≤
    (0.008373383655 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13032) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.157785542642 : ℝ) ≤ √(13032 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13032)
  have hdiv : K / √(13032 : ℝ) ≤ K / 114.157785542642 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.157785542642 ≤ (0.008373383655 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13032.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13032 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13032 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13032 := gPlus_lower 13032
end BstLean.Part269.N13032

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13032
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035346158852 : ℝ) ≤ wn 13032 := by
  have hn : √(13032 : ℝ) ≤ 114.157785542643 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13032 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.157785542643 ≤ 2 / √(13032 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000245354279 : ℝ) ≤ rhoBar 13032 BstLean.Part154.csC ∧
    rhoBar 13032 BstLean.Part154.csC ≤ 0.000245354659 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035346158852 : ℝ) / (1.295212 * 13032) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035346158853 : ℝ) / (1.29521 * 13032) := by gcongr
      _ ≤ (0.000245354659 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13032 BstLean.Part154.csC) ≤ 0.000981478835 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13032 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13032 BstLean.Part154.csC) (piBar (rhoBar 13032 BstLean.Part154.csC)) ≤ 0.000187403318 ∧
    cc1 (rhoBar 13032 BstLean.Part154.csC) (piBar (rhoBar 13032 BstLean.Part154.csC)) ≤ 0.000119246022 ∧
    cc2 (rhoBar 13032 BstLean.Part154.csC) ≤ 0.000069223286 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13032 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13032 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13032 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13032 BstLean.Part154.csC * nuR (rhoBar 13032 BstLean.Part154.csC)) ≤ 0.000490724368 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000245354659 : ℝ) * 0.000981478835 := by gcongr
      _ ≤ (0.000490724368 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13032 BstLean.Part154.csC) * nuR (rhoBar 13032 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000981478835 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13032 BstLean.Part154.csC) * rhoBar 13032 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000245354659 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000245354659 / 2 + 0.399 * 0.000981478835 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000187403318 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000490724368 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119246022 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000245354659 / 1.414213562 := by gcongr
      _ ≤ (0.000069223286 : ℝ) := by norm_num

end BstLean.Part269.N13032

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13032
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13032 BstLean.Part154.csC) (piBar (rhoBar 13032 BstLean.Part154.csC)) ≤ 1.51667E-7 := by
  have hr0 : 0 ≤ rhoBar 13032 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13032 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13032 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13032 BstLean.Part154.csC) (piBar (rhoBar 13032 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13032 BstLean.Part154.csC) (piBar (rhoBar 13032 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13032 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000187403318 : ℝ) ^ 2 + 0.000119246022 ^ 2 + 3 * 0.000069223286 ^ 2 +
        2 * 0.797885 * 0.000187403318 * 0.000119246022 + 2 * 0.000187403318 * 0.000069223286 +
        4 * 0.797885 * 0.000119246022 * 0.000069223286 := by gcongr
    _ ≤ (1.51667E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13032 BstLean.Part154.csC Θ ≤ 0.002560018053 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13032 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13032 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13032 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13032 BstLean.Part154.csC) (piBar (rhoBar 13032 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13032 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035346158853 * 1.51667E-7 / (0.000245354279 : ℝ) := by gcongr
    _ ≤ 0.002560018053 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13032 BstLean.Part154.csC Θ ≤ 0.002839200767 + 0.000646874588 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13032 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13032 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13032 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035346158853 : ℝ) * ((2 * Θ * 0.000245354659 +
        (6863 / 10000) * 0.000245354659 * 13032 * 0.000981478835) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002839200767 + 0.000646874588 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13032 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13032 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13032 0.011 Θ ∧ gammaRatio 13032 0.011 Θ ≤ 0.000084346587 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13032 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035346158853 : ℝ) * 0.525 / ((1 - 0.011) * 13032) := by gcongr
      _ ≤ (0.000084346587 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13032 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13032 0.011 Θ) :=
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
    badAllowance 13032 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000383431726 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13032 BstLean.Part154.csC) 1.22 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 2 (rhoBar 13032 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13032 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13032 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13032 0.011 Θ) 1.12 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 1 (gammaRatio 13032 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13032 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13032 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13032 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13032 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035346158853 : ℝ) * 13032 *
        (1.3781E-8 / 1.1045361 + 1.6832E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000383431726 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13032 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003222632493 + 0.003206892641 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13032

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13032
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13032 BstLean.Part154.csC) (piBar (rhoBar 13032 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13032 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13032 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13032 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13032 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13032 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13032 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13032 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13032 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13032 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13032 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13032 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13032 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13032 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13032 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051804258625 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13032) ≤ 0.010461288956 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13032 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035346158853)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010461288956 + 2 * 0.737676 / 13032) := by gcongr
    _ ≤ (0.051804258625 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13032 12 ≤ 0.0015 := by
  exact BstLean.Part269.S27.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13032

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13032
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560518199823 : ℝ) ≤ plow 13032 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13032) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052412851130)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001344009478) : eMP 13032 0.011 xi bn ≤ 0.001157503928 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13032 : ℝ) * (1 - 0.011))) ≤ 0.000572364178 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001344009478 / (13032 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000572364178 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000572364178 : ℝ) + 3.141593 * 0.052412851130 / (13032 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001157503928 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052412851130)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001344009478) : PiBarMP 13032 12 0.011 xi bn ≤ 0.159163354314 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13032 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036660734827 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.528181523355 : ℝ) ≤ √((13032 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.157785542642 : ℝ) ≤ √(13032 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13032) ≤ 0.122045186814 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036660734827 + 0.052412851130 * 1.772454 / (2 * (113.528181523355 : ℝ))) * (1 + 0.001157503928) +
        8 / (13032 * 114.157785542642) + 0.122045186814 := by gcongr
    _ ≤ (0.159163354314 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052412851130)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001344009478) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280742789961) :
    parallelOracle 13032 0.011 xi bn cd ≤ 0.160128390036 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13032 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13032 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560518199823 : ℝ) ≤ plow 13032 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.157785542642 : ℝ) ≤ √(13032 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280742789961 : ℝ) / (2 * 0.560518199823 * 114.157785542642)) * 0.159163354314 +
        0.280742789961 ^ 2 / (2 * 0.560518199823 * 114.157785542642) := by gcongr
    _ ≤ (0.160128390036 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052412851130) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001344009478)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280742789961) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13032 13032 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560518199823 : ℝ) ≤ plow 13032 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.157785542642 : ℝ) ≤ √(13032 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13032 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13032 Θ 1.22 ≤ 0.011616382481 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.157785542642 := by gcongr <;> linarith
      _ ≤ (0.011616382481 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13032 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13032 13032 0.011 ≤ 0.008373383655 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13032 13032 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13032 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13032 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13032 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13032 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160128390036 + 0.011616382481 + (0.008373383655 : ℝ) *
        (1 + 2 * (0.280742789961 + 0.011616382481) / (0.560518199823 * 114.157785542642))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13032]

end BstLean.Part269.N13032

/-! The original eight local profiles supply actual 13032 moment certificates. -/
namespace BstLean.Part269.N13032
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13032 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13032 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13032 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052412851130 ∧
    0 ≤ bN 13032 BstLean.Part154.csC (groupTheta g) ∧ bN 13032 BstLean.Part154.csC (groupTheta g) ≤ 0.001344009478 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13032 13032 0.011
      (momentAllowance 13032 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13032 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13032 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13032 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13032 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13032 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228938531336 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13032 0.011
      (momentAllowance 13032 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13032 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13032
/-! The actual computed-centre upper energy formula at 13032. -/
namespace BstLean.Part269.N13032
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13032

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13032
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13032)
open BstLean.Part268 (cell13032)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084576728611
  | 2 => 0.085504310369
  | 3 => 0.086427936320
  | 4 => 0.087348532135
  | 5 => 0.088267231839
  | 6 => 0.089185410534
  | 7 => 0.090104720542
  | 8 => 0.091027131066
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13032 13032 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13032 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003224237287 + 0.003208677626 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S27.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13032

/-! Actual upper energy certificates on all 43 source endpoints at 13032. -/
namespace BstLean.Part269.N13032
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13032)
open BstLean.Part268 (cell13032)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13032 (gMinus 13032) (1 - (cell13032 i).lower) ≤ 1 ∧
    energyUpper 13032 (gMinus 13032) (BstLean.Part211.gPlus 13032)
      (finiteEnergy 13032 13032 0.011) (1 - (cell13032 i).lower) ≤
      (cell13032 i).energy := by
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
      have E := BstLean.Part269.S27.uniformEnergy10 (n := 13032) (by norm_num)
        (q := 1 - (cell13032 ⟨10,by decide⟩).lower)
        (by norm_num [cell13032]) (by norm_num [cell13032])
      exact ⟨E.1,E.2.trans (by norm_num [cell13032])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy11 (n := 13032) (by norm_num)
        (q := 1 - (cell13032 ⟨11,by decide⟩).lower)
        (by norm_num [cell13032]) (by norm_num [cell13032])
      exact ⟨E.1,E.2.trans (by norm_num [cell13032])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy12 (n := 13032) (by norm_num)
        (q := 1 - (cell13032 ⟨12,by decide⟩).lower)
        (by norm_num [cell13032]) (by norm_num [cell13032])
      exact ⟨E.1,E.2.trans (by norm_num [cell13032])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy13 (n := 13032) (by norm_num)
        (q := 1 - (cell13032 ⟨13,by decide⟩).lower)
        (by norm_num [cell13032]) (by norm_num [cell13032])
      exact ⟨E.1,E.2.trans (by norm_num [cell13032])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy14 (n := 13032) (by norm_num)
        (q := 1 - (cell13032 ⟨14,by decide⟩).lower)
        (by norm_num [cell13032]) (by norm_num [cell13032])
      exact ⟨E.1,E.2.trans (by norm_num [cell13032])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy15 (n := 13032) (by norm_num)
        (q := 1 - (cell13032 ⟨15,by decide⟩).lower)
        (by norm_num [cell13032]) (by norm_num [cell13032])
      exact ⟨E.1,E.2.trans (by norm_num [cell13032])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy16 (n := 13032) (by norm_num)
        (q := 1 - (cell13032 ⟨16,by decide⟩).lower)
        (by norm_num [cell13032]) (by norm_num [cell13032])
      exact ⟨E.1,E.2.trans (by norm_num [cell13032])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy17 (n := 13032) (by norm_num)
        (q := 1 - (cell13032 ⟨17,by decide⟩).lower)
        (by norm_num [cell13032]) (by norm_num [cell13032])
      exact ⟨E.1,E.2.trans (by norm_num [cell13032])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy18 (n := 13032) (by norm_num)
        (q := 1 - (cell13032 ⟨18,by decide⟩).lower)
        (by norm_num [cell13032]) (by norm_num [cell13032])
      exact ⟨E.1,E.2.trans (by norm_num [cell13032])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy19 (n := 13032) (by norm_num)
        (q := 1 - (cell13032 ⟨19,by decide⟩).lower)
        (by norm_num [cell13032]) (by norm_num [cell13032])
      exact ⟨E.1,E.2.trans (by norm_num [cell13032])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy20 (n := 13032) (by norm_num)
        (q := 1 - (cell13032 ⟨20,by decide⟩).lower)
        (by norm_num [cell13032]) (by norm_num [cell13032])
      exact ⟨E.1,E.2.trans (by norm_num [cell13032])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy21 (n := 13032) (by norm_num)
        (q := 1 - (cell13032 ⟨21,by decide⟩).lower)
        (by norm_num [cell13032]) (by norm_num [cell13032])
      exact ⟨E.1,E.2.trans (by norm_num [cell13032])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy22 (n := 13032) (by norm_num)
        (q := 1 - (cell13032 ⟨22,by decide⟩).lower)
        (by norm_num [cell13032]) (by norm_num [cell13032])
      exact ⟨E.1,E.2.trans (by norm_num [cell13032])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy23 (n := 13032) (by norm_num)
        (q := 1 - (cell13032 ⟨23,by decide⟩).lower)
        (by norm_num [cell13032]) (by norm_num [cell13032])
      exact ⟨E.1,E.2.trans (by norm_num [cell13032])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy24 (n := 13032) (by norm_num)
        (q := 1 - (cell13032 ⟨24,by decide⟩).lower)
        (by norm_num [cell13032]) (by norm_num [cell13032])
      exact ⟨E.1,E.2.trans (by norm_num [cell13032])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy25 (n := 13032) (by norm_num)
        (q := 1 - (cell13032 ⟨25,by decide⟩).lower)
        (by norm_num [cell13032]) (by norm_num [cell13032])
      exact ⟨E.1,E.2.trans (by norm_num [cell13032])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy26 (n := 13032) (by norm_num)
        (q := 1 - (cell13032 ⟨26,by decide⟩).lower)
        (by norm_num [cell13032]) (by norm_num [cell13032])
      exact ⟨E.1,E.2.trans (by norm_num [cell13032])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy27 (n := 13032) (by norm_num)
        (q := 1 - (cell13032 ⟨27,by decide⟩).lower)
        (by norm_num [cell13032]) (by norm_num [cell13032])
      exact ⟨E.1,E.2.trans (by norm_num [cell13032])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy28 (n := 13032) (by norm_num)
        (q := 1 - (cell13032 ⟨28,by decide⟩).lower)
        (by norm_num [cell13032]) (by norm_num [cell13032])
      exact ⟨E.1,E.2.trans (by norm_num [cell13032])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy29 (n := 13032) (by norm_num)
        (q := 1 - (cell13032 ⟨29,by decide⟩).lower)
        (by norm_num [cell13032]) (by norm_num [cell13032])
      exact ⟨E.1,E.2.trans (by norm_num [cell13032])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy30 (n := 13032) (by norm_num)
        (q := 1 - (cell13032 ⟨30,by decide⟩).lower)
        (by norm_num [cell13032]) (by norm_num [cell13032])
      exact ⟨E.1,E.2.trans (by norm_num [cell13032])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy31 (n := 13032) (by norm_num)
        (q := 1 - (cell13032 ⟨31,by decide⟩).lower)
        (by norm_num [cell13032]) (by norm_num [cell13032])
      exact ⟨E.1,E.2.trans (by norm_num [cell13032])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy32 (n := 13032) (by norm_num)
        (q := 1 - (cell13032 ⟨32,by decide⟩).lower)
        (by norm_num [cell13032]) (by norm_num [cell13032])
      exact ⟨E.1,E.2.trans (by norm_num [cell13032])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy33 (n := 13032) (by norm_num)
        (q := 1 - (cell13032 ⟨33,by decide⟩).lower)
        (by norm_num [cell13032]) (by norm_num [cell13032])
      exact ⟨E.1,E.2.trans (by norm_num [cell13032])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy34 (n := 13032) (by norm_num)
        (q := 1 - (cell13032 ⟨34,by decide⟩).lower)
        (by norm_num [cell13032]) (by norm_num [cell13032])
      exact ⟨E.1,E.2.trans (by norm_num [cell13032])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy35 (n := 13032) (by norm_num)
        (q := 1 - (cell13032 ⟨35,by decide⟩).lower)
        (by norm_num [cell13032]) (by norm_num [cell13032])
      exact ⟨E.1,E.2.trans (by norm_num [cell13032])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy36 (n := 13032) (by norm_num)
        (q := 1 - (cell13032 ⟨36,by decide⟩).lower)
        (by norm_num [cell13032]) (by norm_num [cell13032])
      exact ⟨E.1,E.2.trans (by norm_num [cell13032])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy37 (n := 13032) (by norm_num)
        (q := 1 - (cell13032 ⟨37,by decide⟩).lower)
        (by norm_num [cell13032]) (by norm_num [cell13032])
      exact ⟨E.1,E.2.trans (by norm_num [cell13032])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy38 (n := 13032) (by norm_num)
        (q := 1 - (cell13032 ⟨38,by decide⟩).lower)
        (by norm_num [cell13032]) (by norm_num [cell13032])
      exact ⟨E.1,E.2.trans (by norm_num [cell13032])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy39 (n := 13032) (by norm_num)
        (q := 1 - (cell13032 ⟨39,by decide⟩).lower)
        (by norm_num [cell13032]) (by norm_num [cell13032])
      exact ⟨E.1,E.2.trans (by norm_num [cell13032])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy40 (n := 13032) (by norm_num)
        (q := 1 - (cell13032 ⟨40,by decide⟩).lower)
        (by norm_num [cell13032]) (by norm_num [cell13032])
      exact ⟨E.1,E.2.trans (by norm_num [cell13032])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy41 (n := 13032) (by norm_num)
        (q := 1 - (cell13032 ⟨41,by decide⟩).lower)
        (by norm_num [cell13032]) (by norm_num [cell13032])
      exact ⟨E.1,E.2.trans (by norm_num [cell13032])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy42 (n := 13032) (by norm_num)
        (q := 1 - (cell13032 ⟨42,by decide⟩).lower)
        (by norm_num [cell13032]) (by norm_num [cell13032])
      exact ⟨E.1,E.2.trans (by norm_num [cell13032])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy43 (n := 13032) (by norm_num)
        (q := 1 - (cell13032 ⟨43,by decide⟩).lower)
        (by norm_num [cell13032]) (by norm_num [cell13032])
      exact ⟨E.1,E.2.trans (by norm_num [cell13032])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy44 (n := 13032) (by norm_num)
        (q := 1 - (cell13032 ⟨44,by decide⟩).lower)
        (by norm_num [cell13032]) (by norm_num [cell13032])
      exact ⟨E.1,E.2.trans (by norm_num [cell13032])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy45 (n := 13032) (by norm_num)
        (q := 1 - (cell13032 ⟨45,by decide⟩).lower)
        (by norm_num [cell13032]) (by norm_num [cell13032])
      exact ⟨E.1,E.2.trans (by norm_num [cell13032])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy46 (n := 13032) (by norm_num)
        (q := 1 - (cell13032 ⟨46,by decide⟩).lower)
        (by norm_num [cell13032]) (by norm_num [cell13032])
      exact ⟨E.1,E.2.trans (by norm_num [cell13032])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy47 (n := 13032) (by norm_num)
        (q := 1 - (cell13032 ⟨47,by decide⟩).lower)
        (by norm_num [cell13032]) (by norm_num [cell13032])
      exact ⟨E.1,E.2.trans (by norm_num [cell13032])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy48 (n := 13032) (by norm_num)
        (q := 1 - (cell13032 ⟨48,by decide⟩).lower)
        (by norm_num [cell13032]) (by norm_num [cell13032])
      exact ⟨E.1,E.2.trans (by norm_num [cell13032])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy49 (n := 13032) (by norm_num)
        (q := 1 - (cell13032 ⟨49,by decide⟩).lower)
        (by norm_num [cell13032]) (by norm_num [cell13032])
      exact ⟨E.1,E.2.trans (by norm_num [cell13032])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy50 (n := 13032) (by norm_num)
        (q := 1 - (cell13032 ⟨50,by decide⟩).lower)
        (by norm_num [cell13032]) (by norm_num [cell13032])
      exact ⟨E.1,E.2.trans (by norm_num [cell13032])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy51 (n := 13032) (by norm_num)
        (q := 1 - (cell13032 ⟨51,by decide⟩).lower)
        (by norm_num [cell13032]) (by norm_num [cell13032])
      exact ⟨E.1,E.2.trans (by norm_num [cell13032])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy52 (n := 13032) (by norm_num)
        (q := 1 - (cell13032 ⟨52,by decide⟩).lower)
        (by norm_num [cell13032]) (by norm_num [cell13032])
      exact ⟨E.1,E.2.trans (by norm_num [cell13032])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13032

/-! Source-cell containment and simple scalar guards at 13032. -/
namespace BstLean.Part269.N13032
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13032)
open BstLean.Part268 (cell13032)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13032 ⟨10,by decide⟩).lower ∧ (cell13032 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13032 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13032 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13032 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13032 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13032 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13032,cell13032,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13032 ⟨11,by decide⟩).lower ∧ (cell13032 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13032 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13032 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13032 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13032 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13032 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13032,cell13032,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13032 ⟨12,by decide⟩).lower ∧ (cell13032 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13032 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13032 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13032 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13032 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13032 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13032,cell13032,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13032 ⟨13,by decide⟩).lower ∧ (cell13032 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13032 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13032 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13032 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13032 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13032 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13032,cell13032,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13032 ⟨14,by decide⟩).lower ∧ (cell13032 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13032 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13032 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13032 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13032 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13032 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13032,cell13032,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13032 ⟨15,by decide⟩).lower ∧ (cell13032 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13032 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13032 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13032 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13032 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13032 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13032,cell13032,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13032 ⟨16,by decide⟩).lower ∧ (cell13032 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13032 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13032 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13032 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13032 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13032 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13032,cell13032,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13032 ⟨17,by decide⟩).lower ∧ (cell13032 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13032 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13032 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13032 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13032 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13032 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13032,cell13032,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13032 ⟨18,by decide⟩).lower ∧ (cell13032 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13032 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13032 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13032 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13032 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13032 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13032,cell13032,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13032 ⟨19,by decide⟩).lower ∧ (cell13032 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13032 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13032 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13032 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13032 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13032 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13032,cell13032,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13032 ⟨20,by decide⟩).lower ∧ (cell13032 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13032 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13032 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13032 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13032 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13032 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13032,cell13032,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13032 ⟨21,by decide⟩).lower ∧ (cell13032 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13032 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13032 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13032 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13032 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13032 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13032,cell13032,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13032 ⟨22,by decide⟩).lower ∧ (cell13032 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13032 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13032 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13032 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13032 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13032 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13032,cell13032,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13032 ⟨23,by decide⟩).lower ∧ (cell13032 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13032 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13032 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13032 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13032 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13032 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13032,cell13032,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13032 ⟨24,by decide⟩).lower ∧ (cell13032 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13032 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13032 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13032 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13032 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13032 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13032,cell13032,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13032 ⟨25,by decide⟩).lower ∧ (cell13032 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13032 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13032 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13032 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13032 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13032 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13032,cell13032,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13032 ⟨26,by decide⟩).lower ∧ (cell13032 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13032 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13032 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13032 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13032 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13032 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13032,cell13032,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13032 ⟨27,by decide⟩).lower ∧ (cell13032 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13032 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13032 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13032 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13032 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13032 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13032,cell13032,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13032 ⟨28,by decide⟩).lower ∧ (cell13032 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13032 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13032 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13032 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13032 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13032 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13032,cell13032,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13032 ⟨29,by decide⟩).lower ∧ (cell13032 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13032 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13032 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13032 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13032 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13032 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13032,cell13032,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13032 ⟨30,by decide⟩).lower ∧ (cell13032 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13032 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13032 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13032 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13032 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13032 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13032,cell13032,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13032 ⟨31,by decide⟩).lower ∧ (cell13032 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13032 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13032 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13032 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13032 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13032 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13032,cell13032,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13032 ⟨32,by decide⟩).lower ∧ (cell13032 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13032 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13032 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13032 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13032 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13032 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13032,cell13032,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13032 ⟨33,by decide⟩).lower ∧ (cell13032 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13032 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13032 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13032 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13032 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13032 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13032,cell13032,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13032 ⟨34,by decide⟩).lower ∧ (cell13032 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13032 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13032 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13032 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13032 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13032 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13032,cell13032,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13032 ⟨35,by decide⟩).lower ∧ (cell13032 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13032 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13032 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13032 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13032 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13032 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13032,cell13032,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13032 ⟨36,by decide⟩).lower ∧ (cell13032 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13032 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13032 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13032 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13032 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13032 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13032,cell13032,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13032 ⟨37,by decide⟩).lower ∧ (cell13032 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13032 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13032 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13032 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13032 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13032 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13032,cell13032,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13032 ⟨38,by decide⟩).lower ∧ (cell13032 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13032 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13032 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13032 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13032 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13032 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13032,cell13032,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13032 ⟨39,by decide⟩).lower ∧ (cell13032 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13032 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13032 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13032 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13032 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13032 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13032,cell13032,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13032 ⟨40,by decide⟩).lower ∧ (cell13032 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13032 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13032 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13032 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13032 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13032 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13032,cell13032,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13032 ⟨41,by decide⟩).lower ∧ (cell13032 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13032 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13032 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13032 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13032 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13032 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13032,cell13032,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13032 ⟨42,by decide⟩).lower ∧ (cell13032 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13032 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13032 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13032 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13032 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13032 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13032,cell13032,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13032 ⟨43,by decide⟩).lower ∧ (cell13032 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13032 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13032 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13032 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13032 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13032 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13032,cell13032,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13032 ⟨44,by decide⟩).lower ∧ (cell13032 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13032 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13032 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13032 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13032 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13032 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13032,cell13032,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13032 ⟨45,by decide⟩).lower ∧ (cell13032 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13032 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13032 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13032 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13032 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13032 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13032,cell13032,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13032 ⟨46,by decide⟩).lower ∧ (cell13032 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13032 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13032 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13032 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13032 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13032 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13032,cell13032,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13032 ⟨47,by decide⟩).lower ∧ (cell13032 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13032 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13032 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13032 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13032 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13032 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13032,cell13032,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13032 ⟨48,by decide⟩).lower ∧ (cell13032 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13032 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13032 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13032 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13032 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13032 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13032,cell13032,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13032 ⟨49,by decide⟩).lower ∧ (cell13032 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13032 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13032 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13032 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13032 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13032 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13032,cell13032,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13032 ⟨50,by decide⟩).lower ∧ (cell13032 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13032 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13032 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13032 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13032 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13032 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13032,cell13032,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13032 ⟨51,by decide⟩).lower ∧ (cell13032 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13032 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13032 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13032 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13032 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13032 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13032,cell13032,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13032 ⟨52,by decide⟩).lower ∧ (cell13032 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13032 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13032 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13032 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13032 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13032 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13032,cell13032,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13032 i).lower ∧
    (cell13032 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13032 i).upper ≤ (0.532 : ℝ) ∧
    (cell13032 i).centre ≤ (0.1 : ℝ) ∧ (cell13032 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13032 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13032 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13032

/-! The local source numeric instances at 13032 have no network premises. -/
namespace BstLean.Part269.N13032
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13032)
open BstLean.Part268 (cell13032)

noncomputable def sourceNumerics13032 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13032 (cell13032 i)
      scalarRow13032.M scalarRow13032.H scalarRow13032.xi := by
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
    energy_allowance := scalarRow13032.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13032]
    centre_nonneg := (scalarRow13032.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D27.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13032])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13032
/-! Actual 13033 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13033
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13033 ≤ (1.035344791027 : ℝ) := by
  have hr : (114.162165361384 : ℝ) ≤ √(13033 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.162165361384 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13033 13033 (11 / 1000) ≤
    (0.008373062408 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13033) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.162165361384 : ℝ) ≤ √(13033 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13033)
  have hdiv : K / √(13033 : ℝ) ≤ K / 114.162165361384 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.162165361384 ≤ (0.008373062408 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13033.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13033 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13033 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13033 := gPlus_lower 13033
end BstLean.Part269.N13033

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13033
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035344791026 : ℝ) ≤ wn 13033 := by
  have hn : √(13033 : ℝ) ≤ 114.162165361385 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13033 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.162165361385 ≤ 2 / √(13033 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000245335129 : ℝ) ≤ rhoBar 13033 BstLean.Part154.csC ∧
    rhoBar 13033 BstLean.Part154.csC ≤ 0.000245335509 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035344791026 : ℝ) / (1.295212 * 13033) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035344791027 : ℝ) / (1.29521 * 13033) := by gcongr
      _ ≤ (0.000245335509 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13033 BstLean.Part154.csC) ≤ 0.000981402226 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13033 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13033 BstLean.Part154.csC) (piBar (rhoBar 13033 BstLean.Part154.csC)) ≤ 0.000187388690 ∧
    cc1 (rhoBar 13033 BstLean.Part154.csC) (piBar (rhoBar 13033 BstLean.Part154.csC)) ≤ 0.000119236715 ∧
    cc2 (rhoBar 13033 BstLean.Part154.csC) ≤ 0.000069217883 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13033 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13033 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13033 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13033 BstLean.Part154.csC * nuR (rhoBar 13033 BstLean.Part154.csC)) ≤ 0.000490686066 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000245335509 : ℝ) * 0.000981402226 := by gcongr
      _ ≤ (0.000490686066 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13033 BstLean.Part154.csC) * nuR (rhoBar 13033 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000981402226 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13033 BstLean.Part154.csC) * rhoBar 13033 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000245335509 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000245335509 / 2 + 0.399 * 0.000981402226 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000187388690 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000490686066 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119236715 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000245335509 / 1.414213562 := by gcongr
      _ ≤ (0.000069217883 : ℝ) := by norm_num

end BstLean.Part269.N13033

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13033
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13033 BstLean.Part154.csC) (piBar (rhoBar 13033 BstLean.Part154.csC)) ≤ 1.51643E-7 := by
  have hr0 : 0 ≤ rhoBar 13033 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13033 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13033 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13033 BstLean.Part154.csC) (piBar (rhoBar 13033 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13033 BstLean.Part154.csC) (piBar (rhoBar 13033 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13033 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000187388690 : ℝ) ^ 2 + 0.000119236715 ^ 2 + 3 * 0.000069217883 ^ 2 +
        2 * 0.797885 * 0.000187388690 * 0.000119236715 + 2 * 0.000187388690 * 0.000069217883 +
        4 * 0.797885 * 0.000119236715 * 0.000069217883 := by gcongr
    _ ≤ (1.51643E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13033 BstLean.Part154.csC Θ ≤ 0.002559809365 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13033 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13033 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13033 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13033 BstLean.Part154.csC) (piBar (rhoBar 13033 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13033 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035344791027 * 1.51643E-7 / (0.000245335129 : ℝ) := by gcongr
    _ ≤ 0.002559809365 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13033 BstLean.Part154.csC Θ ≤ 0.002838971651 + 0.000646823245 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13033 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13033 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13033 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035344791027 : ℝ) * ((2 * Θ * 0.000245335509 +
        (6863 / 10000) * 0.000245335509 * 13033 * 0.000981402226) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002838971651 + 0.000646823245 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13033 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13033 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13033 0.011 Θ ∧ gammaRatio 13033 0.011 Θ ≤ 0.000084340004 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13033 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035344791027 : ℝ) * 0.525 / ((1 - 0.011) * 13033) := by gcongr
      _ ≤ (0.000084340004 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13033 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13033 0.011 Θ) :=
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
    badAllowance 13033 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000383431726 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13033 BstLean.Part154.csC) 1.22 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 2 (rhoBar 13033 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13033 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13033 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13033 0.011 Θ) 1.12 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 1 (gammaRatio 13033 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13033 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13033 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13033 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13033 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035344791027 : ℝ) * 13033 *
        (1.3781E-8 / 1.1045361 + 1.6832E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000383431726 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13033 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003222403377 + 0.003206632610 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13033

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13033
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13033 BstLean.Part154.csC) (piBar (rhoBar 13033 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13033 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13033 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13033 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13033 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13033 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13033 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13033 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13033 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13033 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13033 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13033 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13033 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13033 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13033 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051802249885 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13033) ≤ 0.010460887610 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13033 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035344791027)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010460887610 + 2 * 0.737676 / 13033) := by gcongr
    _ ≤ (0.051802249885 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13033 12 ≤ 0.0015 := by
  exact BstLean.Part269.S27.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13033

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13033
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560518242768 : ℝ) ≤ plow 13033 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13033) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052412485498)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001343899917) : eMP 13033 0.011 xi bn ≤ 0.001157412283 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13033 : ℝ) * (1 - 0.011))) ≤ 0.000572318890 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001343899917 / (13033 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000572318890 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000572318890 : ℝ) + 3.141593 * 0.052412485498 / (13033 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001157412283 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052412485498)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001343899917) : PiBarMP 13033 12 0.011 xi bn ≤ 0.159157153460 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13033 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036659240541 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.532537186482 : ℝ) ≤ √((13033 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.162165361384 : ℝ) ≤ √(13033 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13033) ≤ 0.122040504564 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036659240541 + 0.052412485498 * 1.772454 / (2 * (113.532537186482 : ℝ))) * (1 + 0.001157412283) +
        8 / (13033 * 114.162165361384) + 0.122040504564 := by gcongr
    _ ≤ (0.159157153460 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052412485498)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001343899917) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280739982682) :
    parallelOracle 13033 0.011 xi bn cd ≤ 0.160122122675 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13033 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13033 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560518242768 : ℝ) ≤ plow 13033 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.162165361384 : ℝ) ≤ √(13033 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280739982682 : ℝ) / (2 * 0.560518242768 * 114.162165361384)) * 0.159157153460 +
        0.280739982682 ^ 2 / (2 * 0.560518242768 * 114.162165361384) := by gcongr
    _ ≤ (0.160122122675 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052412485498) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001343899917)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280739982682) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13033 13033 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560518242768 : ℝ) ≤ plow 13033 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.162165361384 : ℝ) ≤ √(13033 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13033 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13033 Θ 1.22 ≤ 0.011615936820 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.162165361384 := by gcongr <;> linarith
      _ ≤ (0.011615936820 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13033 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13033 13033 0.011 ≤ 0.008373062408 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13033 13033 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13033 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13033 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13033 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13033 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160122122675 + 0.011615936820 + (0.008373062408 : ℝ) *
        (1 + 2 * (0.280739982682 + 0.011615936820) / (0.560518242768 * 114.162165361384))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13033]

end BstLean.Part269.N13033

/-! The original eight local profiles supply actual 13033 moment certificates. -/
namespace BstLean.Part269.N13033
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13033 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13033 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13033 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052412485498 ∧
    0 ≤ bN 13033 BstLean.Part154.csC (groupTheta g) ∧ bN 13033 BstLean.Part154.csC (groupTheta g) ≤ 0.001343899917 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13033 13033 0.011
      (momentAllowance 13033 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13033 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13033 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13033 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13033 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13033 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228937732797 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13033 0.011
      (momentAllowance 13033 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13033 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13033
/-! The actual computed-centre upper energy formula at 13033. -/
namespace BstLean.Part269.N13033
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13033

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13033
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13033)
open BstLean.Part268 (cell13033)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084574135853
  | 2 => 0.085501683958
  | 3 => 0.086425271214
  | 4 => 0.087345822108
  | 5 => 0.088264469262
  | 6 => 0.089182586128
  | 7 => 0.090101823103
  | 8 => 0.091024147155
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13033 13033 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13033 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003224237287 + 0.003208677626 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S27.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13033

/-! Actual upper energy certificates on all 43 source endpoints at 13033. -/
namespace BstLean.Part269.N13033
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13033)
open BstLean.Part268 (cell13033)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13033 (gMinus 13033) (1 - (cell13033 i).lower) ≤ 1 ∧
    energyUpper 13033 (gMinus 13033) (BstLean.Part211.gPlus 13033)
      (finiteEnergy 13033 13033 0.011) (1 - (cell13033 i).lower) ≤
      (cell13033 i).energy := by
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
      have E := BstLean.Part269.S27.uniformEnergy10 (n := 13033) (by norm_num)
        (q := 1 - (cell13033 ⟨10,by decide⟩).lower)
        (by norm_num [cell13033]) (by norm_num [cell13033])
      exact ⟨E.1,E.2.trans (by norm_num [cell13033])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy11 (n := 13033) (by norm_num)
        (q := 1 - (cell13033 ⟨11,by decide⟩).lower)
        (by norm_num [cell13033]) (by norm_num [cell13033])
      exact ⟨E.1,E.2.trans (by norm_num [cell13033])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy12 (n := 13033) (by norm_num)
        (q := 1 - (cell13033 ⟨12,by decide⟩).lower)
        (by norm_num [cell13033]) (by norm_num [cell13033])
      exact ⟨E.1,E.2.trans (by norm_num [cell13033])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy13 (n := 13033) (by norm_num)
        (q := 1 - (cell13033 ⟨13,by decide⟩).lower)
        (by norm_num [cell13033]) (by norm_num [cell13033])
      exact ⟨E.1,E.2.trans (by norm_num [cell13033])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy14 (n := 13033) (by norm_num)
        (q := 1 - (cell13033 ⟨14,by decide⟩).lower)
        (by norm_num [cell13033]) (by norm_num [cell13033])
      exact ⟨E.1,E.2.trans (by norm_num [cell13033])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy15 (n := 13033) (by norm_num)
        (q := 1 - (cell13033 ⟨15,by decide⟩).lower)
        (by norm_num [cell13033]) (by norm_num [cell13033])
      exact ⟨E.1,E.2.trans (by norm_num [cell13033])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy16 (n := 13033) (by norm_num)
        (q := 1 - (cell13033 ⟨16,by decide⟩).lower)
        (by norm_num [cell13033]) (by norm_num [cell13033])
      exact ⟨E.1,E.2.trans (by norm_num [cell13033])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy17 (n := 13033) (by norm_num)
        (q := 1 - (cell13033 ⟨17,by decide⟩).lower)
        (by norm_num [cell13033]) (by norm_num [cell13033])
      exact ⟨E.1,E.2.trans (by norm_num [cell13033])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy18 (n := 13033) (by norm_num)
        (q := 1 - (cell13033 ⟨18,by decide⟩).lower)
        (by norm_num [cell13033]) (by norm_num [cell13033])
      exact ⟨E.1,E.2.trans (by norm_num [cell13033])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy19 (n := 13033) (by norm_num)
        (q := 1 - (cell13033 ⟨19,by decide⟩).lower)
        (by norm_num [cell13033]) (by norm_num [cell13033])
      exact ⟨E.1,E.2.trans (by norm_num [cell13033])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy20 (n := 13033) (by norm_num)
        (q := 1 - (cell13033 ⟨20,by decide⟩).lower)
        (by norm_num [cell13033]) (by norm_num [cell13033])
      exact ⟨E.1,E.2.trans (by norm_num [cell13033])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy21 (n := 13033) (by norm_num)
        (q := 1 - (cell13033 ⟨21,by decide⟩).lower)
        (by norm_num [cell13033]) (by norm_num [cell13033])
      exact ⟨E.1,E.2.trans (by norm_num [cell13033])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy22 (n := 13033) (by norm_num)
        (q := 1 - (cell13033 ⟨22,by decide⟩).lower)
        (by norm_num [cell13033]) (by norm_num [cell13033])
      exact ⟨E.1,E.2.trans (by norm_num [cell13033])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy23 (n := 13033) (by norm_num)
        (q := 1 - (cell13033 ⟨23,by decide⟩).lower)
        (by norm_num [cell13033]) (by norm_num [cell13033])
      exact ⟨E.1,E.2.trans (by norm_num [cell13033])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy24 (n := 13033) (by norm_num)
        (q := 1 - (cell13033 ⟨24,by decide⟩).lower)
        (by norm_num [cell13033]) (by norm_num [cell13033])
      exact ⟨E.1,E.2.trans (by norm_num [cell13033])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy25 (n := 13033) (by norm_num)
        (q := 1 - (cell13033 ⟨25,by decide⟩).lower)
        (by norm_num [cell13033]) (by norm_num [cell13033])
      exact ⟨E.1,E.2.trans (by norm_num [cell13033])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy26 (n := 13033) (by norm_num)
        (q := 1 - (cell13033 ⟨26,by decide⟩).lower)
        (by norm_num [cell13033]) (by norm_num [cell13033])
      exact ⟨E.1,E.2.trans (by norm_num [cell13033])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy27 (n := 13033) (by norm_num)
        (q := 1 - (cell13033 ⟨27,by decide⟩).lower)
        (by norm_num [cell13033]) (by norm_num [cell13033])
      exact ⟨E.1,E.2.trans (by norm_num [cell13033])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy28 (n := 13033) (by norm_num)
        (q := 1 - (cell13033 ⟨28,by decide⟩).lower)
        (by norm_num [cell13033]) (by norm_num [cell13033])
      exact ⟨E.1,E.2.trans (by norm_num [cell13033])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy29 (n := 13033) (by norm_num)
        (q := 1 - (cell13033 ⟨29,by decide⟩).lower)
        (by norm_num [cell13033]) (by norm_num [cell13033])
      exact ⟨E.1,E.2.trans (by norm_num [cell13033])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy30 (n := 13033) (by norm_num)
        (q := 1 - (cell13033 ⟨30,by decide⟩).lower)
        (by norm_num [cell13033]) (by norm_num [cell13033])
      exact ⟨E.1,E.2.trans (by norm_num [cell13033])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy31 (n := 13033) (by norm_num)
        (q := 1 - (cell13033 ⟨31,by decide⟩).lower)
        (by norm_num [cell13033]) (by norm_num [cell13033])
      exact ⟨E.1,E.2.trans (by norm_num [cell13033])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy32 (n := 13033) (by norm_num)
        (q := 1 - (cell13033 ⟨32,by decide⟩).lower)
        (by norm_num [cell13033]) (by norm_num [cell13033])
      exact ⟨E.1,E.2.trans (by norm_num [cell13033])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy33 (n := 13033) (by norm_num)
        (q := 1 - (cell13033 ⟨33,by decide⟩).lower)
        (by norm_num [cell13033]) (by norm_num [cell13033])
      exact ⟨E.1,E.2.trans (by norm_num [cell13033])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy34 (n := 13033) (by norm_num)
        (q := 1 - (cell13033 ⟨34,by decide⟩).lower)
        (by norm_num [cell13033]) (by norm_num [cell13033])
      exact ⟨E.1,E.2.trans (by norm_num [cell13033])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy35 (n := 13033) (by norm_num)
        (q := 1 - (cell13033 ⟨35,by decide⟩).lower)
        (by norm_num [cell13033]) (by norm_num [cell13033])
      exact ⟨E.1,E.2.trans (by norm_num [cell13033])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy36 (n := 13033) (by norm_num)
        (q := 1 - (cell13033 ⟨36,by decide⟩).lower)
        (by norm_num [cell13033]) (by norm_num [cell13033])
      exact ⟨E.1,E.2.trans (by norm_num [cell13033])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy37 (n := 13033) (by norm_num)
        (q := 1 - (cell13033 ⟨37,by decide⟩).lower)
        (by norm_num [cell13033]) (by norm_num [cell13033])
      exact ⟨E.1,E.2.trans (by norm_num [cell13033])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy38 (n := 13033) (by norm_num)
        (q := 1 - (cell13033 ⟨38,by decide⟩).lower)
        (by norm_num [cell13033]) (by norm_num [cell13033])
      exact ⟨E.1,E.2.trans (by norm_num [cell13033])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy39 (n := 13033) (by norm_num)
        (q := 1 - (cell13033 ⟨39,by decide⟩).lower)
        (by norm_num [cell13033]) (by norm_num [cell13033])
      exact ⟨E.1,E.2.trans (by norm_num [cell13033])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy40 (n := 13033) (by norm_num)
        (q := 1 - (cell13033 ⟨40,by decide⟩).lower)
        (by norm_num [cell13033]) (by norm_num [cell13033])
      exact ⟨E.1,E.2.trans (by norm_num [cell13033])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy41 (n := 13033) (by norm_num)
        (q := 1 - (cell13033 ⟨41,by decide⟩).lower)
        (by norm_num [cell13033]) (by norm_num [cell13033])
      exact ⟨E.1,E.2.trans (by norm_num [cell13033])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy42 (n := 13033) (by norm_num)
        (q := 1 - (cell13033 ⟨42,by decide⟩).lower)
        (by norm_num [cell13033]) (by norm_num [cell13033])
      exact ⟨E.1,E.2.trans (by norm_num [cell13033])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy43 (n := 13033) (by norm_num)
        (q := 1 - (cell13033 ⟨43,by decide⟩).lower)
        (by norm_num [cell13033]) (by norm_num [cell13033])
      exact ⟨E.1,E.2.trans (by norm_num [cell13033])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy44 (n := 13033) (by norm_num)
        (q := 1 - (cell13033 ⟨44,by decide⟩).lower)
        (by norm_num [cell13033]) (by norm_num [cell13033])
      exact ⟨E.1,E.2.trans (by norm_num [cell13033])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy45 (n := 13033) (by norm_num)
        (q := 1 - (cell13033 ⟨45,by decide⟩).lower)
        (by norm_num [cell13033]) (by norm_num [cell13033])
      exact ⟨E.1,E.2.trans (by norm_num [cell13033])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy46 (n := 13033) (by norm_num)
        (q := 1 - (cell13033 ⟨46,by decide⟩).lower)
        (by norm_num [cell13033]) (by norm_num [cell13033])
      exact ⟨E.1,E.2.trans (by norm_num [cell13033])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy47 (n := 13033) (by norm_num)
        (q := 1 - (cell13033 ⟨47,by decide⟩).lower)
        (by norm_num [cell13033]) (by norm_num [cell13033])
      exact ⟨E.1,E.2.trans (by norm_num [cell13033])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy48 (n := 13033) (by norm_num)
        (q := 1 - (cell13033 ⟨48,by decide⟩).lower)
        (by norm_num [cell13033]) (by norm_num [cell13033])
      exact ⟨E.1,E.2.trans (by norm_num [cell13033])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy49 (n := 13033) (by norm_num)
        (q := 1 - (cell13033 ⟨49,by decide⟩).lower)
        (by norm_num [cell13033]) (by norm_num [cell13033])
      exact ⟨E.1,E.2.trans (by norm_num [cell13033])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy50 (n := 13033) (by norm_num)
        (q := 1 - (cell13033 ⟨50,by decide⟩).lower)
        (by norm_num [cell13033]) (by norm_num [cell13033])
      exact ⟨E.1,E.2.trans (by norm_num [cell13033])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy51 (n := 13033) (by norm_num)
        (q := 1 - (cell13033 ⟨51,by decide⟩).lower)
        (by norm_num [cell13033]) (by norm_num [cell13033])
      exact ⟨E.1,E.2.trans (by norm_num [cell13033])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy52 (n := 13033) (by norm_num)
        (q := 1 - (cell13033 ⟨52,by decide⟩).lower)
        (by norm_num [cell13033]) (by norm_num [cell13033])
      exact ⟨E.1,E.2.trans (by norm_num [cell13033])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13033

/-! Source-cell containment and simple scalar guards at 13033. -/
namespace BstLean.Part269.N13033
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13033)
open BstLean.Part268 (cell13033)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13033 ⟨10,by decide⟩).lower ∧ (cell13033 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13033 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13033 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13033 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13033 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13033 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13033,cell13033,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13033 ⟨11,by decide⟩).lower ∧ (cell13033 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13033 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13033 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13033 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13033 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13033 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13033,cell13033,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13033 ⟨12,by decide⟩).lower ∧ (cell13033 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13033 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13033 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13033 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13033 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13033 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13033,cell13033,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13033 ⟨13,by decide⟩).lower ∧ (cell13033 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13033 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13033 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13033 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13033 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13033 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13033,cell13033,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13033 ⟨14,by decide⟩).lower ∧ (cell13033 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13033 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13033 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13033 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13033 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13033 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13033,cell13033,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13033 ⟨15,by decide⟩).lower ∧ (cell13033 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13033 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13033 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13033 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13033 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13033 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13033,cell13033,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13033 ⟨16,by decide⟩).lower ∧ (cell13033 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13033 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13033 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13033 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13033 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13033 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13033,cell13033,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13033 ⟨17,by decide⟩).lower ∧ (cell13033 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13033 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13033 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13033 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13033 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13033 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13033,cell13033,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13033 ⟨18,by decide⟩).lower ∧ (cell13033 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13033 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13033 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13033 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13033 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13033 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13033,cell13033,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13033 ⟨19,by decide⟩).lower ∧ (cell13033 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13033 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13033 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13033 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13033 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13033 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13033,cell13033,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13033 ⟨20,by decide⟩).lower ∧ (cell13033 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13033 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13033 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13033 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13033 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13033 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13033,cell13033,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13033 ⟨21,by decide⟩).lower ∧ (cell13033 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13033 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13033 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13033 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13033 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13033 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13033,cell13033,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13033 ⟨22,by decide⟩).lower ∧ (cell13033 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13033 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13033 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13033 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13033 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13033 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13033,cell13033,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13033 ⟨23,by decide⟩).lower ∧ (cell13033 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13033 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13033 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13033 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13033 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13033 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13033,cell13033,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13033 ⟨24,by decide⟩).lower ∧ (cell13033 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13033 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13033 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13033 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13033 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13033 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13033,cell13033,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13033 ⟨25,by decide⟩).lower ∧ (cell13033 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13033 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13033 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13033 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13033 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13033 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13033,cell13033,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13033 ⟨26,by decide⟩).lower ∧ (cell13033 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13033 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13033 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13033 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13033 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13033 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13033,cell13033,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13033 ⟨27,by decide⟩).lower ∧ (cell13033 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13033 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13033 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13033 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13033 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13033 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13033,cell13033,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13033 ⟨28,by decide⟩).lower ∧ (cell13033 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13033 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13033 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13033 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13033 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13033 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13033,cell13033,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13033 ⟨29,by decide⟩).lower ∧ (cell13033 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13033 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13033 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13033 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13033 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13033 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13033,cell13033,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13033 ⟨30,by decide⟩).lower ∧ (cell13033 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13033 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13033 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13033 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13033 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13033 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13033,cell13033,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13033 ⟨31,by decide⟩).lower ∧ (cell13033 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13033 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13033 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13033 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13033 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13033 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13033,cell13033,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13033 ⟨32,by decide⟩).lower ∧ (cell13033 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13033 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13033 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13033 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13033 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13033 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13033,cell13033,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13033 ⟨33,by decide⟩).lower ∧ (cell13033 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13033 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13033 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13033 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13033 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13033 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13033,cell13033,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13033 ⟨34,by decide⟩).lower ∧ (cell13033 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13033 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13033 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13033 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13033 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13033 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13033,cell13033,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13033 ⟨35,by decide⟩).lower ∧ (cell13033 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13033 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13033 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13033 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13033 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13033 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13033,cell13033,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13033 ⟨36,by decide⟩).lower ∧ (cell13033 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13033 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13033 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13033 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13033 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13033 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13033,cell13033,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13033 ⟨37,by decide⟩).lower ∧ (cell13033 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13033 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13033 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13033 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13033 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13033 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13033,cell13033,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13033 ⟨38,by decide⟩).lower ∧ (cell13033 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13033 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13033 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13033 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13033 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13033 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13033,cell13033,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13033 ⟨39,by decide⟩).lower ∧ (cell13033 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13033 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13033 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13033 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13033 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13033 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13033,cell13033,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13033 ⟨40,by decide⟩).lower ∧ (cell13033 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13033 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13033 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13033 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13033 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13033 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13033,cell13033,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13033 ⟨41,by decide⟩).lower ∧ (cell13033 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13033 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13033 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13033 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13033 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13033 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13033,cell13033,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13033 ⟨42,by decide⟩).lower ∧ (cell13033 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13033 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13033 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13033 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13033 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13033 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13033,cell13033,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13033 ⟨43,by decide⟩).lower ∧ (cell13033 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13033 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13033 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13033 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13033 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13033 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13033,cell13033,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13033 ⟨44,by decide⟩).lower ∧ (cell13033 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13033 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13033 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13033 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13033 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13033 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13033,cell13033,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13033 ⟨45,by decide⟩).lower ∧ (cell13033 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13033 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13033 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13033 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13033 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13033 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13033,cell13033,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13033 ⟨46,by decide⟩).lower ∧ (cell13033 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13033 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13033 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13033 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13033 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13033 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13033,cell13033,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13033 ⟨47,by decide⟩).lower ∧ (cell13033 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13033 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13033 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13033 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13033 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13033 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13033,cell13033,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13033 ⟨48,by decide⟩).lower ∧ (cell13033 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13033 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13033 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13033 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13033 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13033 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13033,cell13033,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13033 ⟨49,by decide⟩).lower ∧ (cell13033 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13033 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13033 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13033 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13033 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13033 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13033,cell13033,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13033 ⟨50,by decide⟩).lower ∧ (cell13033 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13033 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13033 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13033 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13033 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13033 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13033,cell13033,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13033 ⟨51,by decide⟩).lower ∧ (cell13033 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13033 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13033 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13033 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13033 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13033 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13033,cell13033,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13033 ⟨52,by decide⟩).lower ∧ (cell13033 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13033 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13033 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13033 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13033 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13033 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13033,cell13033,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13033 i).lower ∧
    (cell13033 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13033 i).upper ≤ (0.532 : ℝ) ∧
    (cell13033 i).centre ≤ (0.1 : ℝ) ∧ (cell13033 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13033 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13033 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13033

/-! The local source numeric instances at 13033 have no network premises. -/
namespace BstLean.Part269.N13033
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13033)
open BstLean.Part268 (cell13033)

noncomputable def sourceNumerics13033 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13033 (cell13033 i)
      scalarRow13033.M scalarRow13033.H scalarRow13033.xi := by
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
    energy_allowance := scalarRow13033.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13033]
    centre_nonneg := (scalarRow13033.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D27.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13033])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13033
/-! Actual 13034 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13034
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13034 ≤ (1.035343423359 : ℝ) := by
  have hr : (114.166545012100 : ℝ) ≤ √(13034 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.166545012100 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13034 13034 (11 / 1000) ≤
    (0.008372741199 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13034) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.166545012100 : ℝ) ≤ √(13034 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13034)
  have hdiv : K / √(13034 : ℝ) ≤ K / 114.166545012100 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.166545012100 ≤ (0.008372741199 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13034.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13034 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13034 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13034 := gPlus_lower 13034
end BstLean.Part269.N13034

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13034
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035343423358 : ℝ) ≤ wn 13034 := by
  have hn : √(13034 : ℝ) ≤ 114.166545012101 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13034 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.166545012101 ≤ 2 / √(13034 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000245315982 : ℝ) ≤ rhoBar 13034 BstLean.Part154.csC ∧
    rhoBar 13034 BstLean.Part154.csC ≤ 0.000245316362 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035343423358 : ℝ) / (1.295212 * 13034) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035343423359 : ℝ) / (1.29521 * 13034) := by gcongr
      _ ≤ (0.000245316362 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13034 BstLean.Part154.csC) ≤ 0.000981325629 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13034 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13034 BstLean.Part154.csC) (piBar (rhoBar 13034 BstLean.Part154.csC)) ≤ 0.000187374065 ∧
    cc1 (rhoBar 13034 BstLean.Part154.csC) (piBar (rhoBar 13034 BstLean.Part154.csC)) ≤ 0.000119227409 ∧
    cc2 (rhoBar 13034 BstLean.Part154.csC) ≤ 0.000069212481 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13034 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13034 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13034 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13034 BstLean.Part154.csC * nuR (rhoBar 13034 BstLean.Part154.csC)) ≤ 0.000490647770 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000245316362 : ℝ) * 0.000981325629 := by gcongr
      _ ≤ (0.000490647770 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13034 BstLean.Part154.csC) * nuR (rhoBar 13034 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000981325629 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13034 BstLean.Part154.csC) * rhoBar 13034 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000245316362 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000245316362 / 2 + 0.399 * 0.000981325629 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000187374065 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000490647770 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119227409 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000245316362 / 1.414213562 := by gcongr
      _ ≤ (0.000069212481 : ℝ) := by norm_num

end BstLean.Part269.N13034

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13034
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13034 BstLean.Part154.csC) (piBar (rhoBar 13034 BstLean.Part154.csC)) ≤ 1.51619E-7 := by
  have hr0 : 0 ≤ rhoBar 13034 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13034 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13034 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13034 BstLean.Part154.csC) (piBar (rhoBar 13034 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13034 BstLean.Part154.csC) (piBar (rhoBar 13034 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13034 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000187374065 : ℝ) ^ 2 + 0.000119227409 ^ 2 + 3 * 0.000069212481 ^ 2 +
        2 * 0.797885 * 0.000187374065 * 0.000119227409 + 2 * 0.000187374065 * 0.000069212481 +
        4 * 0.797885 * 0.000119227409 * 0.000069212481 := by gcongr
    _ ≤ (1.51619E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13034 BstLean.Part154.csC Θ ≤ 0.002559600614 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13034 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13034 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13034 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13034 BstLean.Part154.csC) (piBar (rhoBar 13034 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13034 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035343423359 * 1.51619E-7 / (0.000245315982 : ℝ) := by gcongr
    _ ≤ 0.002559600614 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13034 BstLean.Part154.csC Θ ≤ 0.002838742571 + 0.000646771910 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13034 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13034 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13034 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035343423359 : ℝ) * ((2 * Θ * 0.000245316362 +
        (6863 / 10000) * 0.000245316362 * 13034 * 0.000981325629) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002838742571 + 0.000646771910 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13034 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13034 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13034 0.011 Θ ∧ gammaRatio 13034 0.011 Θ ≤ 0.000084333422 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13034 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035343423359 : ℝ) * 0.525 / ((1 - 0.011) * 13034) := by gcongr
      _ ≤ (0.000084333422 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13034 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13034 0.011 Θ) :=
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
    badAllowance 13034 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000383431726 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13034 BstLean.Part154.csC) 1.22 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 2 (rhoBar 13034 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13034 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13034 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13034 0.011 Θ) 1.12 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 1 (gammaRatio 13034 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13034 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13034 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13034 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13034 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035343423359 : ℝ) * 13034 *
        (1.3781E-8 / 1.1045361 + 1.6832E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000383431726 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13034 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003222174297 + 0.003206372524 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13034

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13034
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13034 BstLean.Part154.csC) (piBar (rhoBar 13034 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13034 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13034 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13034 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13034 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13034 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13034 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13034 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13034 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13034 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13034 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13034 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13034 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13034 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13034 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051800241376 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13034) ≤ 0.010460486310 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13034 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035343423359)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010460486310 + 2 * 0.737676 / 13034) := by gcongr
    _ ≤ (0.051800241376 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13034 12 ≤ 0.0015 := by
  exact BstLean.Part269.S27.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13034

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13034
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560518285706 : ℝ) ≤ plow 13034 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13034) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052412119873)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001343790323) : eMP 13034 0.011 xi bn ≤ 0.001157320632 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13034 : ℝ) * (1 - 0.011))) ≤ 0.000572273599 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001343790323 / (13034 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000572273599 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000572273599 : ℝ) + 3.141593 * 0.052412119873 / (13034 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001157320632 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052412119873)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001343790323) : PiBarMP 13034 12 0.011 xi bn ≤ 0.159150952636 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13034 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036657745744 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.536892682510 : ℝ) ≤ √((13034 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.166545012100 : ℝ) ≤ √(13034 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13034) ≤ 0.122035822853 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036657745744 + 0.052412119873 * 1.772454 / (2 * (113.536892682510 : ℝ))) * (1 + 0.001157320632) +
        8 / (13034 * 114.166545012100) + 0.122035822853 := by gcongr
    _ ≤ (0.159150952636 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052412119873)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001343790323) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280737175647) :
    parallelOracle 13034 0.011 xi bn cd ≤ 0.160115855352 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13034 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13034 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560518285706 : ℝ) ≤ plow 13034 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.166545012100 : ℝ) ≤ √(13034 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280737175647 : ℝ) / (2 * 0.560518285706 * 114.166545012100)) * 0.159150952636 +
        0.280737175647 ^ 2 / (2 * 0.560518285706 * 114.166545012100) := by gcongr
    _ ≤ (0.160115855352 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052412119873) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001343790323)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280737175647) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13034 13034 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560518285706 : ℝ) ≤ plow 13034 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.166545012100 : ℝ) ≤ √(13034 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13034 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13034 Θ 1.22 ≤ 0.011615491210 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.166545012100 := by gcongr <;> linarith
      _ ≤ (0.011615491210 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13034 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13034 13034 0.011 ≤ 0.008372741199 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13034 13034 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13034 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13034 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13034 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13034 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160115855352 + 0.011615491210 + (0.008372741199 : ℝ) *
        (1 + 2 * (0.280737175647 + 0.011615491210) / (0.560518285706 * 114.166545012100))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13034]

end BstLean.Part269.N13034

/-! The original eight local profiles supply actual 13034 moment certificates. -/
namespace BstLean.Part269.N13034
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13034 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13034 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13034 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052412119873 ∧
    0 ≤ bN 13034 BstLean.Part154.csC (groupTheta g) ∧ bN 13034 BstLean.Part154.csC (groupTheta g) ≤ 0.001343790323 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13034 13034 0.011
      (momentAllowance 13034 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13034 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13034 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13034 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13034 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13034 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228936934271 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13034 0.011
      (momentAllowance 13034 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13034 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13034
/-! The actual computed-centre upper energy formula at 13034. -/
namespace BstLean.Part269.N13034
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13034

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13034
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13034)
open BstLean.Part268 (cell13034)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084571543879
  | 2 => 0.085499058357
  | 3 => 0.086422606954
  | 4 => 0.087343112969
  | 5 => 0.088261707623
  | 6 => 0.089179762724
  | 7 => 0.090098926742
  | 8 => 0.091021164413
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13034 13034 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13034 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003224237287 + 0.003208677626 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S27.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13034

/-! Actual upper energy certificates on all 43 source endpoints at 13034. -/
namespace BstLean.Part269.N13034
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13034)
open BstLean.Part268 (cell13034)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13034 (gMinus 13034) (1 - (cell13034 i).lower) ≤ 1 ∧
    energyUpper 13034 (gMinus 13034) (BstLean.Part211.gPlus 13034)
      (finiteEnergy 13034 13034 0.011) (1 - (cell13034 i).lower) ≤
      (cell13034 i).energy := by
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
      have E := BstLean.Part269.S27.uniformEnergy10 (n := 13034) (by norm_num)
        (q := 1 - (cell13034 ⟨10,by decide⟩).lower)
        (by norm_num [cell13034]) (by norm_num [cell13034])
      exact ⟨E.1,E.2.trans (by norm_num [cell13034])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy11 (n := 13034) (by norm_num)
        (q := 1 - (cell13034 ⟨11,by decide⟩).lower)
        (by norm_num [cell13034]) (by norm_num [cell13034])
      exact ⟨E.1,E.2.trans (by norm_num [cell13034])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy12 (n := 13034) (by norm_num)
        (q := 1 - (cell13034 ⟨12,by decide⟩).lower)
        (by norm_num [cell13034]) (by norm_num [cell13034])
      exact ⟨E.1,E.2.trans (by norm_num [cell13034])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy13 (n := 13034) (by norm_num)
        (q := 1 - (cell13034 ⟨13,by decide⟩).lower)
        (by norm_num [cell13034]) (by norm_num [cell13034])
      exact ⟨E.1,E.2.trans (by norm_num [cell13034])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy14 (n := 13034) (by norm_num)
        (q := 1 - (cell13034 ⟨14,by decide⟩).lower)
        (by norm_num [cell13034]) (by norm_num [cell13034])
      exact ⟨E.1,E.2.trans (by norm_num [cell13034])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy15 (n := 13034) (by norm_num)
        (q := 1 - (cell13034 ⟨15,by decide⟩).lower)
        (by norm_num [cell13034]) (by norm_num [cell13034])
      exact ⟨E.1,E.2.trans (by norm_num [cell13034])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy16 (n := 13034) (by norm_num)
        (q := 1 - (cell13034 ⟨16,by decide⟩).lower)
        (by norm_num [cell13034]) (by norm_num [cell13034])
      exact ⟨E.1,E.2.trans (by norm_num [cell13034])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy17 (n := 13034) (by norm_num)
        (q := 1 - (cell13034 ⟨17,by decide⟩).lower)
        (by norm_num [cell13034]) (by norm_num [cell13034])
      exact ⟨E.1,E.2.trans (by norm_num [cell13034])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy18 (n := 13034) (by norm_num)
        (q := 1 - (cell13034 ⟨18,by decide⟩).lower)
        (by norm_num [cell13034]) (by norm_num [cell13034])
      exact ⟨E.1,E.2.trans (by norm_num [cell13034])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy19 (n := 13034) (by norm_num)
        (q := 1 - (cell13034 ⟨19,by decide⟩).lower)
        (by norm_num [cell13034]) (by norm_num [cell13034])
      exact ⟨E.1,E.2.trans (by norm_num [cell13034])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy20 (n := 13034) (by norm_num)
        (q := 1 - (cell13034 ⟨20,by decide⟩).lower)
        (by norm_num [cell13034]) (by norm_num [cell13034])
      exact ⟨E.1,E.2.trans (by norm_num [cell13034])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy21 (n := 13034) (by norm_num)
        (q := 1 - (cell13034 ⟨21,by decide⟩).lower)
        (by norm_num [cell13034]) (by norm_num [cell13034])
      exact ⟨E.1,E.2.trans (by norm_num [cell13034])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy22 (n := 13034) (by norm_num)
        (q := 1 - (cell13034 ⟨22,by decide⟩).lower)
        (by norm_num [cell13034]) (by norm_num [cell13034])
      exact ⟨E.1,E.2.trans (by norm_num [cell13034])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy23 (n := 13034) (by norm_num)
        (q := 1 - (cell13034 ⟨23,by decide⟩).lower)
        (by norm_num [cell13034]) (by norm_num [cell13034])
      exact ⟨E.1,E.2.trans (by norm_num [cell13034])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy24 (n := 13034) (by norm_num)
        (q := 1 - (cell13034 ⟨24,by decide⟩).lower)
        (by norm_num [cell13034]) (by norm_num [cell13034])
      exact ⟨E.1,E.2.trans (by norm_num [cell13034])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy25 (n := 13034) (by norm_num)
        (q := 1 - (cell13034 ⟨25,by decide⟩).lower)
        (by norm_num [cell13034]) (by norm_num [cell13034])
      exact ⟨E.1,E.2.trans (by norm_num [cell13034])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy26 (n := 13034) (by norm_num)
        (q := 1 - (cell13034 ⟨26,by decide⟩).lower)
        (by norm_num [cell13034]) (by norm_num [cell13034])
      exact ⟨E.1,E.2.trans (by norm_num [cell13034])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy27 (n := 13034) (by norm_num)
        (q := 1 - (cell13034 ⟨27,by decide⟩).lower)
        (by norm_num [cell13034]) (by norm_num [cell13034])
      exact ⟨E.1,E.2.trans (by norm_num [cell13034])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy28 (n := 13034) (by norm_num)
        (q := 1 - (cell13034 ⟨28,by decide⟩).lower)
        (by norm_num [cell13034]) (by norm_num [cell13034])
      exact ⟨E.1,E.2.trans (by norm_num [cell13034])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy29 (n := 13034) (by norm_num)
        (q := 1 - (cell13034 ⟨29,by decide⟩).lower)
        (by norm_num [cell13034]) (by norm_num [cell13034])
      exact ⟨E.1,E.2.trans (by norm_num [cell13034])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy30 (n := 13034) (by norm_num)
        (q := 1 - (cell13034 ⟨30,by decide⟩).lower)
        (by norm_num [cell13034]) (by norm_num [cell13034])
      exact ⟨E.1,E.2.trans (by norm_num [cell13034])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy31 (n := 13034) (by norm_num)
        (q := 1 - (cell13034 ⟨31,by decide⟩).lower)
        (by norm_num [cell13034]) (by norm_num [cell13034])
      exact ⟨E.1,E.2.trans (by norm_num [cell13034])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy32 (n := 13034) (by norm_num)
        (q := 1 - (cell13034 ⟨32,by decide⟩).lower)
        (by norm_num [cell13034]) (by norm_num [cell13034])
      exact ⟨E.1,E.2.trans (by norm_num [cell13034])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy33 (n := 13034) (by norm_num)
        (q := 1 - (cell13034 ⟨33,by decide⟩).lower)
        (by norm_num [cell13034]) (by norm_num [cell13034])
      exact ⟨E.1,E.2.trans (by norm_num [cell13034])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy34 (n := 13034) (by norm_num)
        (q := 1 - (cell13034 ⟨34,by decide⟩).lower)
        (by norm_num [cell13034]) (by norm_num [cell13034])
      exact ⟨E.1,E.2.trans (by norm_num [cell13034])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy35 (n := 13034) (by norm_num)
        (q := 1 - (cell13034 ⟨35,by decide⟩).lower)
        (by norm_num [cell13034]) (by norm_num [cell13034])
      exact ⟨E.1,E.2.trans (by norm_num [cell13034])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy36 (n := 13034) (by norm_num)
        (q := 1 - (cell13034 ⟨36,by decide⟩).lower)
        (by norm_num [cell13034]) (by norm_num [cell13034])
      exact ⟨E.1,E.2.trans (by norm_num [cell13034])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy37 (n := 13034) (by norm_num)
        (q := 1 - (cell13034 ⟨37,by decide⟩).lower)
        (by norm_num [cell13034]) (by norm_num [cell13034])
      exact ⟨E.1,E.2.trans (by norm_num [cell13034])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy38 (n := 13034) (by norm_num)
        (q := 1 - (cell13034 ⟨38,by decide⟩).lower)
        (by norm_num [cell13034]) (by norm_num [cell13034])
      exact ⟨E.1,E.2.trans (by norm_num [cell13034])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy39 (n := 13034) (by norm_num)
        (q := 1 - (cell13034 ⟨39,by decide⟩).lower)
        (by norm_num [cell13034]) (by norm_num [cell13034])
      exact ⟨E.1,E.2.trans (by norm_num [cell13034])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy40 (n := 13034) (by norm_num)
        (q := 1 - (cell13034 ⟨40,by decide⟩).lower)
        (by norm_num [cell13034]) (by norm_num [cell13034])
      exact ⟨E.1,E.2.trans (by norm_num [cell13034])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy41 (n := 13034) (by norm_num)
        (q := 1 - (cell13034 ⟨41,by decide⟩).lower)
        (by norm_num [cell13034]) (by norm_num [cell13034])
      exact ⟨E.1,E.2.trans (by norm_num [cell13034])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy42 (n := 13034) (by norm_num)
        (q := 1 - (cell13034 ⟨42,by decide⟩).lower)
        (by norm_num [cell13034]) (by norm_num [cell13034])
      exact ⟨E.1,E.2.trans (by norm_num [cell13034])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy43 (n := 13034) (by norm_num)
        (q := 1 - (cell13034 ⟨43,by decide⟩).lower)
        (by norm_num [cell13034]) (by norm_num [cell13034])
      exact ⟨E.1,E.2.trans (by norm_num [cell13034])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy44 (n := 13034) (by norm_num)
        (q := 1 - (cell13034 ⟨44,by decide⟩).lower)
        (by norm_num [cell13034]) (by norm_num [cell13034])
      exact ⟨E.1,E.2.trans (by norm_num [cell13034])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy45 (n := 13034) (by norm_num)
        (q := 1 - (cell13034 ⟨45,by decide⟩).lower)
        (by norm_num [cell13034]) (by norm_num [cell13034])
      exact ⟨E.1,E.2.trans (by norm_num [cell13034])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy46 (n := 13034) (by norm_num)
        (q := 1 - (cell13034 ⟨46,by decide⟩).lower)
        (by norm_num [cell13034]) (by norm_num [cell13034])
      exact ⟨E.1,E.2.trans (by norm_num [cell13034])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy47 (n := 13034) (by norm_num)
        (q := 1 - (cell13034 ⟨47,by decide⟩).lower)
        (by norm_num [cell13034]) (by norm_num [cell13034])
      exact ⟨E.1,E.2.trans (by norm_num [cell13034])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy48 (n := 13034) (by norm_num)
        (q := 1 - (cell13034 ⟨48,by decide⟩).lower)
        (by norm_num [cell13034]) (by norm_num [cell13034])
      exact ⟨E.1,E.2.trans (by norm_num [cell13034])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy49 (n := 13034) (by norm_num)
        (q := 1 - (cell13034 ⟨49,by decide⟩).lower)
        (by norm_num [cell13034]) (by norm_num [cell13034])
      exact ⟨E.1,E.2.trans (by norm_num [cell13034])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy50 (n := 13034) (by norm_num)
        (q := 1 - (cell13034 ⟨50,by decide⟩).lower)
        (by norm_num [cell13034]) (by norm_num [cell13034])
      exact ⟨E.1,E.2.trans (by norm_num [cell13034])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy51 (n := 13034) (by norm_num)
        (q := 1 - (cell13034 ⟨51,by decide⟩).lower)
        (by norm_num [cell13034]) (by norm_num [cell13034])
      exact ⟨E.1,E.2.trans (by norm_num [cell13034])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy52 (n := 13034) (by norm_num)
        (q := 1 - (cell13034 ⟨52,by decide⟩).lower)
        (by norm_num [cell13034]) (by norm_num [cell13034])
      exact ⟨E.1,E.2.trans (by norm_num [cell13034])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13034

/-! Source-cell containment and simple scalar guards at 13034. -/
namespace BstLean.Part269.N13034
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13034)
open BstLean.Part268 (cell13034)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13034 ⟨10,by decide⟩).lower ∧ (cell13034 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13034 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13034 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13034 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13034 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13034 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13034,cell13034,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13034 ⟨11,by decide⟩).lower ∧ (cell13034 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13034 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13034 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13034 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13034 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13034 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13034,cell13034,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13034 ⟨12,by decide⟩).lower ∧ (cell13034 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13034 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13034 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13034 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13034 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13034 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13034,cell13034,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13034 ⟨13,by decide⟩).lower ∧ (cell13034 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13034 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13034 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13034 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13034 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13034 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13034,cell13034,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13034 ⟨14,by decide⟩).lower ∧ (cell13034 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13034 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13034 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13034 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13034 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13034 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13034,cell13034,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13034 ⟨15,by decide⟩).lower ∧ (cell13034 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13034 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13034 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13034 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13034 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13034 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13034,cell13034,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13034 ⟨16,by decide⟩).lower ∧ (cell13034 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13034 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13034 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13034 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13034 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13034 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13034,cell13034,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13034 ⟨17,by decide⟩).lower ∧ (cell13034 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13034 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13034 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13034 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13034 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13034 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13034,cell13034,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13034 ⟨18,by decide⟩).lower ∧ (cell13034 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13034 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13034 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13034 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13034 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13034 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13034,cell13034,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13034 ⟨19,by decide⟩).lower ∧ (cell13034 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13034 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13034 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13034 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13034 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13034 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13034,cell13034,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13034 ⟨20,by decide⟩).lower ∧ (cell13034 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13034 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13034 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13034 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13034 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13034 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13034,cell13034,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13034 ⟨21,by decide⟩).lower ∧ (cell13034 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13034 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13034 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13034 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13034 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13034 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13034,cell13034,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13034 ⟨22,by decide⟩).lower ∧ (cell13034 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13034 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13034 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13034 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13034 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13034 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13034,cell13034,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13034 ⟨23,by decide⟩).lower ∧ (cell13034 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13034 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13034 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13034 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13034 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13034 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13034,cell13034,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13034 ⟨24,by decide⟩).lower ∧ (cell13034 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13034 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13034 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13034 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13034 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13034 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13034,cell13034,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13034 ⟨25,by decide⟩).lower ∧ (cell13034 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13034 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13034 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13034 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13034 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13034 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13034,cell13034,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13034 ⟨26,by decide⟩).lower ∧ (cell13034 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13034 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13034 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13034 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13034 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13034 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13034,cell13034,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13034 ⟨27,by decide⟩).lower ∧ (cell13034 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13034 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13034 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13034 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13034 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13034 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13034,cell13034,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13034 ⟨28,by decide⟩).lower ∧ (cell13034 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13034 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13034 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13034 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13034 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13034 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13034,cell13034,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13034 ⟨29,by decide⟩).lower ∧ (cell13034 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13034 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13034 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13034 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13034 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13034 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13034,cell13034,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13034 ⟨30,by decide⟩).lower ∧ (cell13034 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13034 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13034 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13034 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13034 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13034 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13034,cell13034,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13034 ⟨31,by decide⟩).lower ∧ (cell13034 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13034 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13034 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13034 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13034 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13034 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13034,cell13034,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13034 ⟨32,by decide⟩).lower ∧ (cell13034 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13034 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13034 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13034 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13034 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13034 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13034,cell13034,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13034 ⟨33,by decide⟩).lower ∧ (cell13034 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13034 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13034 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13034 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13034 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13034 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13034,cell13034,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13034 ⟨34,by decide⟩).lower ∧ (cell13034 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13034 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13034 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13034 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13034 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13034 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13034,cell13034,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13034 ⟨35,by decide⟩).lower ∧ (cell13034 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13034 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13034 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13034 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13034 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13034 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13034,cell13034,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13034 ⟨36,by decide⟩).lower ∧ (cell13034 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13034 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13034 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13034 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13034 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13034 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13034,cell13034,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13034 ⟨37,by decide⟩).lower ∧ (cell13034 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13034 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13034 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13034 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13034 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13034 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13034,cell13034,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13034 ⟨38,by decide⟩).lower ∧ (cell13034 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13034 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13034 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13034 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13034 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13034 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13034,cell13034,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13034 ⟨39,by decide⟩).lower ∧ (cell13034 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13034 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13034 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13034 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13034 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13034 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13034,cell13034,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13034 ⟨40,by decide⟩).lower ∧ (cell13034 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13034 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13034 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13034 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13034 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13034 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13034,cell13034,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13034 ⟨41,by decide⟩).lower ∧ (cell13034 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13034 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13034 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13034 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13034 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13034 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13034,cell13034,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13034 ⟨42,by decide⟩).lower ∧ (cell13034 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13034 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13034 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13034 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13034 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13034 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13034,cell13034,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13034 ⟨43,by decide⟩).lower ∧ (cell13034 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13034 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13034 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13034 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13034 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13034 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13034,cell13034,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13034 ⟨44,by decide⟩).lower ∧ (cell13034 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13034 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13034 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13034 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13034 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13034 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13034,cell13034,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13034 ⟨45,by decide⟩).lower ∧ (cell13034 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13034 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13034 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13034 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13034 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13034 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13034,cell13034,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13034 ⟨46,by decide⟩).lower ∧ (cell13034 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13034 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13034 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13034 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13034 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13034 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13034,cell13034,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13034 ⟨47,by decide⟩).lower ∧ (cell13034 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13034 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13034 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13034 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13034 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13034 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13034,cell13034,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13034 ⟨48,by decide⟩).lower ∧ (cell13034 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13034 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13034 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13034 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13034 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13034 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13034,cell13034,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13034 ⟨49,by decide⟩).lower ∧ (cell13034 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13034 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13034 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13034 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13034 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13034 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13034,cell13034,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13034 ⟨50,by decide⟩).lower ∧ (cell13034 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13034 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13034 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13034 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13034 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13034 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13034,cell13034,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13034 ⟨51,by decide⟩).lower ∧ (cell13034 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13034 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13034 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13034 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13034 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13034 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13034,cell13034,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13034 ⟨52,by decide⟩).lower ∧ (cell13034 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13034 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13034 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13034 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13034 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13034 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13034,cell13034,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13034 i).lower ∧
    (cell13034 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13034 i).upper ≤ (0.532 : ℝ) ∧
    (cell13034 i).centre ≤ (0.1 : ℝ) ∧ (cell13034 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13034 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13034 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13034

/-! The local source numeric instances at 13034 have no network premises. -/
namespace BstLean.Part269.N13034
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13034)
open BstLean.Part268 (cell13034)

noncomputable def sourceNumerics13034 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13034 (cell13034 i)
      scalarRow13034.M scalarRow13034.H scalarRow13034.xi := by
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
    energy_allowance := scalarRow13034.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13034]
    centre_nonneg := (scalarRow13034.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D27.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13034])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13034
/-! Actual 13035 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13035
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13035 ≤ (1.035342055849 : ℝ) := by
  have hr : (114.170924494811 : ℝ) ≤ √(13035 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.170924494811 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13035 13035 (11 / 1000) ≤
    (0.008372420026 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13035) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.170924494811 : ℝ) ≤ √(13035 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13035)
  have hdiv : K / √(13035 : ℝ) ≤ K / 114.170924494811 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.170924494811 ≤ (0.008372420026 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13035.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13035 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13035 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13035 := gPlus_lower 13035
end BstLean.Part269.N13035

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13035
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035342055848 : ℝ) ≤ wn 13035 := by
  have hn : √(13035 : ℝ) ≤ 114.170924494812 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13035 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.170924494812 ≤ 2 / √(13035 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000245296839 : ℝ) ≤ rhoBar 13035 BstLean.Part154.csC ∧
    rhoBar 13035 BstLean.Part154.csC ≤ 0.000245297218 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035342055848 : ℝ) / (1.295212 * 13035) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035342055849 : ℝ) / (1.29521 * 13035) := by gcongr
      _ ≤ (0.000245297218 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13035 BstLean.Part154.csC) ≤ 0.000981249043 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13035 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13035 BstLean.Part154.csC) (piBar (rhoBar 13035 BstLean.Part154.csC)) ≤ 0.000187359442 ∧
    cc1 (rhoBar 13035 BstLean.Part154.csC) (piBar (rhoBar 13035 BstLean.Part154.csC)) ≤ 0.000119218104 ∧
    cc2 (rhoBar 13035 BstLean.Part154.csC) ≤ 0.000069207080 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13035 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13035 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13035 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13035 BstLean.Part154.csC * nuR (rhoBar 13035 BstLean.Part154.csC)) ≤ 0.000490609479 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000245297218 : ℝ) * 0.000981249043 := by gcongr
      _ ≤ (0.000490609479 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13035 BstLean.Part154.csC) * nuR (rhoBar 13035 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000981249043 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13035 BstLean.Part154.csC) * rhoBar 13035 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000245297218 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000245297218 / 2 + 0.399 * 0.000981249043 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000187359442 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000490609479 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119218104 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000245297218 / 1.414213562 := by gcongr
      _ ≤ (0.000069207080 : ℝ) := by norm_num

end BstLean.Part269.N13035

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13035
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13035 BstLean.Part154.csC) (piBar (rhoBar 13035 BstLean.Part154.csC)) ≤ 1.51596E-7 := by
  have hr0 : 0 ≤ rhoBar 13035 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13035 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13035 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13035 BstLean.Part154.csC) (piBar (rhoBar 13035 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13035 BstLean.Part154.csC) (piBar (rhoBar 13035 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13035 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000187359442 : ℝ) ^ 2 + 0.000119218104 ^ 2 + 3 * 0.000069207080 ^ 2 +
        2 * 0.797885 * 0.000187359442 * 0.000119218104 + 2 * 0.000187359442 * 0.000069207080 +
        4 * 0.797885 * 0.000119218104 * 0.000069207080 := by gcongr
    _ ≤ (1.51596E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13035 BstLean.Part154.csC Θ ≤ 0.002559408673 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13035 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13035 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13035 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13035 BstLean.Part154.csC) (piBar (rhoBar 13035 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13035 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035342055849 * 1.51596E-7 / (0.000245296839 : ℝ) := by gcongr
    _ ≤ 0.002559408673 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13035 BstLean.Part154.csC Θ ≤ 0.002838513525 + 0.000646720583 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13035 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13035 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13035 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035342055849 : ℝ) * ((2 * Θ * 0.000245297218 +
        (6863 / 10000) * 0.000245297218 * 13035 * 0.000981249043) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002838513525 + 0.000646720583 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13035 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13035 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13035 0.011 Θ ∧ gammaRatio 13035 0.011 Θ ≤ 0.000084326841 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13035 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035342055849 : ℝ) * 0.525 / ((1 - 0.011) * 13035) := by gcongr
      _ ≤ (0.000084326841 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13035 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13035 0.011 Θ) :=
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
    badAllowance 13035 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000383431726 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13035 BstLean.Part154.csC) 1.22 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 2 (rhoBar 13035 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13035 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13035 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13035 0.011 Θ) 1.12 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 1 (gammaRatio 13035 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13035 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13035 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13035 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13035 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035342055849 : ℝ) * 13035 *
        (1.3781E-8 / 1.1045361 + 1.6832E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000383431726 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13035 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003221945251 + 0.003206129256 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13035

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13035
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13035 BstLean.Part154.csC) (piBar (rhoBar 13035 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13035 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13035 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13035 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13035 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13035 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13035 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13035 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13035 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13035 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13035 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13035 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13035 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13035 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13035 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051798233099 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13035) ≤ 0.010460085056 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13035 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035342055849)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010460085056 + 2 * 0.737676 / 13035) := by gcongr
    _ ≤ (0.051798233099 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13035 12 ≤ 0.0015 := by
  exact BstLean.Part269.S27.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13035

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13035
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560518328638 : ℝ) ≤ plow 13035 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13035) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052411763111)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001343689554) : eMP 13035 0.011 xi bn ≤ 0.001157232749 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13035 : ℝ) * (1 - 0.011))) ≤ 0.000572230191 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001343689554 / (13035 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000572230191 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000572230191 : ℝ) + 3.141593 * 0.052411763111 / (13035 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001157232749 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052411763111)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001343689554) : PiBarMP 13035 12 0.011 xi bn ≤ 0.159144873014 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13035 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036656371261 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.541248011460 : ℝ) ≤ √((13035 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.170924494811 : ℝ) ≤ √(13035 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13035) ≤ 0.122031141680 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036656371261 + 0.052411763111 * 1.772454 / (2 * (113.541248011460 : ℝ))) * (1 + 0.001157232749) +
        8 / (13035 * 114.170924494811) + 0.122031141680 := by gcongr
    _ ≤ (0.159144873014 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052411763111)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001343689554) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280734388197) :
    parallelOracle 13035 0.011 xi bn cd ≤ 0.160109709614 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13035 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13035 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560518328638 : ℝ) ≤ plow 13035 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.170924494811 : ℝ) ≤ √(13035 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280734388197 : ℝ) / (2 * 0.560518328638 * 114.170924494811)) * 0.159144873014 +
        0.280734388197 ^ 2 / (2 * 0.560518328638 * 114.170924494811) := by gcongr
    _ ≤ (0.160109709614 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052411763111) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001343689554)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280734388197) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13035 13035 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560518328638 : ℝ) ≤ plow 13035 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.170924494811 : ℝ) ≤ √(13035 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13035 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13035 Θ 1.22 ≤ 0.011615045651 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.170924494811 := by gcongr <;> linarith
      _ ≤ (0.011615045651 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13035 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13035 13035 0.011 ≤ 0.008372420026 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13035 13035 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13035 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13035 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13035 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13035 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160109709614 + 0.011615045651 + (0.008372420026 : ℝ) *
        (1 + 2 * (0.280734388197 + 0.011615045651) / (0.560518328638 * 114.170924494811))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13035]

end BstLean.Part269.N13035

/-! The original eight local profiles supply actual 13035 moment certificates. -/
namespace BstLean.Part269.N13035
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13035 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13035 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13035 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052411763111 ∧
    0 ≤ bN 13035 BstLean.Part154.csC (groupTheta g) ∧ bN 13035 BstLean.Part154.csC (groupTheta g) ≤ 0.001343689554 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13035 13035 0.011
      (momentAllowance 13035 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13035 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13035 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13035 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13035 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13035 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228936155098 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13035 0.011
      (momentAllowance 13035 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13035 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13035
/-! The actual computed-centre upper energy formula at 13035. -/
namespace BstLean.Part269.N13035
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13035

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13035
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13035)
open BstLean.Part268 (cell13035)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084568952688
  | 2 => 0.085496433567
  | 3 => 0.086419943537
  | 4 => 0.087340404715
  | 5 => 0.088258946922
  | 6 => 0.089176940319
  | 7 => 0.090096031457
  | 8 => 0.091018182840
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13035 13035 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13035 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003224237287 + 0.003208677626 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S27.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13035

/-! Actual upper energy certificates on all 43 source endpoints at 13035. -/
namespace BstLean.Part269.N13035
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13035)
open BstLean.Part268 (cell13035)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13035 (gMinus 13035) (1 - (cell13035 i).lower) ≤ 1 ∧
    energyUpper 13035 (gMinus 13035) (BstLean.Part211.gPlus 13035)
      (finiteEnergy 13035 13035 0.011) (1 - (cell13035 i).lower) ≤
      (cell13035 i).energy := by
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
      have E := BstLean.Part269.S27.uniformEnergy10 (n := 13035) (by norm_num)
        (q := 1 - (cell13035 ⟨10,by decide⟩).lower)
        (by norm_num [cell13035]) (by norm_num [cell13035])
      exact ⟨E.1,E.2.trans (by norm_num [cell13035])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy11 (n := 13035) (by norm_num)
        (q := 1 - (cell13035 ⟨11,by decide⟩).lower)
        (by norm_num [cell13035]) (by norm_num [cell13035])
      exact ⟨E.1,E.2.trans (by norm_num [cell13035])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy12 (n := 13035) (by norm_num)
        (q := 1 - (cell13035 ⟨12,by decide⟩).lower)
        (by norm_num [cell13035]) (by norm_num [cell13035])
      exact ⟨E.1,E.2.trans (by norm_num [cell13035])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy13 (n := 13035) (by norm_num)
        (q := 1 - (cell13035 ⟨13,by decide⟩).lower)
        (by norm_num [cell13035]) (by norm_num [cell13035])
      exact ⟨E.1,E.2.trans (by norm_num [cell13035])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy14 (n := 13035) (by norm_num)
        (q := 1 - (cell13035 ⟨14,by decide⟩).lower)
        (by norm_num [cell13035]) (by norm_num [cell13035])
      exact ⟨E.1,E.2.trans (by norm_num [cell13035])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy15 (n := 13035) (by norm_num)
        (q := 1 - (cell13035 ⟨15,by decide⟩).lower)
        (by norm_num [cell13035]) (by norm_num [cell13035])
      exact ⟨E.1,E.2.trans (by norm_num [cell13035])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy16 (n := 13035) (by norm_num)
        (q := 1 - (cell13035 ⟨16,by decide⟩).lower)
        (by norm_num [cell13035]) (by norm_num [cell13035])
      exact ⟨E.1,E.2.trans (by norm_num [cell13035])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy17 (n := 13035) (by norm_num)
        (q := 1 - (cell13035 ⟨17,by decide⟩).lower)
        (by norm_num [cell13035]) (by norm_num [cell13035])
      exact ⟨E.1,E.2.trans (by norm_num [cell13035])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy18 (n := 13035) (by norm_num)
        (q := 1 - (cell13035 ⟨18,by decide⟩).lower)
        (by norm_num [cell13035]) (by norm_num [cell13035])
      exact ⟨E.1,E.2.trans (by norm_num [cell13035])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy19 (n := 13035) (by norm_num)
        (q := 1 - (cell13035 ⟨19,by decide⟩).lower)
        (by norm_num [cell13035]) (by norm_num [cell13035])
      exact ⟨E.1,E.2.trans (by norm_num [cell13035])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy20 (n := 13035) (by norm_num)
        (q := 1 - (cell13035 ⟨20,by decide⟩).lower)
        (by norm_num [cell13035]) (by norm_num [cell13035])
      exact ⟨E.1,E.2.trans (by norm_num [cell13035])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy21 (n := 13035) (by norm_num)
        (q := 1 - (cell13035 ⟨21,by decide⟩).lower)
        (by norm_num [cell13035]) (by norm_num [cell13035])
      exact ⟨E.1,E.2.trans (by norm_num [cell13035])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy22 (n := 13035) (by norm_num)
        (q := 1 - (cell13035 ⟨22,by decide⟩).lower)
        (by norm_num [cell13035]) (by norm_num [cell13035])
      exact ⟨E.1,E.2.trans (by norm_num [cell13035])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy23 (n := 13035) (by norm_num)
        (q := 1 - (cell13035 ⟨23,by decide⟩).lower)
        (by norm_num [cell13035]) (by norm_num [cell13035])
      exact ⟨E.1,E.2.trans (by norm_num [cell13035])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy24 (n := 13035) (by norm_num)
        (q := 1 - (cell13035 ⟨24,by decide⟩).lower)
        (by norm_num [cell13035]) (by norm_num [cell13035])
      exact ⟨E.1,E.2.trans (by norm_num [cell13035])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy25 (n := 13035) (by norm_num)
        (q := 1 - (cell13035 ⟨25,by decide⟩).lower)
        (by norm_num [cell13035]) (by norm_num [cell13035])
      exact ⟨E.1,E.2.trans (by norm_num [cell13035])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy26 (n := 13035) (by norm_num)
        (q := 1 - (cell13035 ⟨26,by decide⟩).lower)
        (by norm_num [cell13035]) (by norm_num [cell13035])
      exact ⟨E.1,E.2.trans (by norm_num [cell13035])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy27 (n := 13035) (by norm_num)
        (q := 1 - (cell13035 ⟨27,by decide⟩).lower)
        (by norm_num [cell13035]) (by norm_num [cell13035])
      exact ⟨E.1,E.2.trans (by norm_num [cell13035])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy28 (n := 13035) (by norm_num)
        (q := 1 - (cell13035 ⟨28,by decide⟩).lower)
        (by norm_num [cell13035]) (by norm_num [cell13035])
      exact ⟨E.1,E.2.trans (by norm_num [cell13035])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy29 (n := 13035) (by norm_num)
        (q := 1 - (cell13035 ⟨29,by decide⟩).lower)
        (by norm_num [cell13035]) (by norm_num [cell13035])
      exact ⟨E.1,E.2.trans (by norm_num [cell13035])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy30 (n := 13035) (by norm_num)
        (q := 1 - (cell13035 ⟨30,by decide⟩).lower)
        (by norm_num [cell13035]) (by norm_num [cell13035])
      exact ⟨E.1,E.2.trans (by norm_num [cell13035])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy31 (n := 13035) (by norm_num)
        (q := 1 - (cell13035 ⟨31,by decide⟩).lower)
        (by norm_num [cell13035]) (by norm_num [cell13035])
      exact ⟨E.1,E.2.trans (by norm_num [cell13035])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy32 (n := 13035) (by norm_num)
        (q := 1 - (cell13035 ⟨32,by decide⟩).lower)
        (by norm_num [cell13035]) (by norm_num [cell13035])
      exact ⟨E.1,E.2.trans (by norm_num [cell13035])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy33 (n := 13035) (by norm_num)
        (q := 1 - (cell13035 ⟨33,by decide⟩).lower)
        (by norm_num [cell13035]) (by norm_num [cell13035])
      exact ⟨E.1,E.2.trans (by norm_num [cell13035])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy34 (n := 13035) (by norm_num)
        (q := 1 - (cell13035 ⟨34,by decide⟩).lower)
        (by norm_num [cell13035]) (by norm_num [cell13035])
      exact ⟨E.1,E.2.trans (by norm_num [cell13035])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy35 (n := 13035) (by norm_num)
        (q := 1 - (cell13035 ⟨35,by decide⟩).lower)
        (by norm_num [cell13035]) (by norm_num [cell13035])
      exact ⟨E.1,E.2.trans (by norm_num [cell13035])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy36 (n := 13035) (by norm_num)
        (q := 1 - (cell13035 ⟨36,by decide⟩).lower)
        (by norm_num [cell13035]) (by norm_num [cell13035])
      exact ⟨E.1,E.2.trans (by norm_num [cell13035])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy37 (n := 13035) (by norm_num)
        (q := 1 - (cell13035 ⟨37,by decide⟩).lower)
        (by norm_num [cell13035]) (by norm_num [cell13035])
      exact ⟨E.1,E.2.trans (by norm_num [cell13035])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy38 (n := 13035) (by norm_num)
        (q := 1 - (cell13035 ⟨38,by decide⟩).lower)
        (by norm_num [cell13035]) (by norm_num [cell13035])
      exact ⟨E.1,E.2.trans (by norm_num [cell13035])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy39 (n := 13035) (by norm_num)
        (q := 1 - (cell13035 ⟨39,by decide⟩).lower)
        (by norm_num [cell13035]) (by norm_num [cell13035])
      exact ⟨E.1,E.2.trans (by norm_num [cell13035])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy40 (n := 13035) (by norm_num)
        (q := 1 - (cell13035 ⟨40,by decide⟩).lower)
        (by norm_num [cell13035]) (by norm_num [cell13035])
      exact ⟨E.1,E.2.trans (by norm_num [cell13035])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy41 (n := 13035) (by norm_num)
        (q := 1 - (cell13035 ⟨41,by decide⟩).lower)
        (by norm_num [cell13035]) (by norm_num [cell13035])
      exact ⟨E.1,E.2.trans (by norm_num [cell13035])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy42 (n := 13035) (by norm_num)
        (q := 1 - (cell13035 ⟨42,by decide⟩).lower)
        (by norm_num [cell13035]) (by norm_num [cell13035])
      exact ⟨E.1,E.2.trans (by norm_num [cell13035])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy43 (n := 13035) (by norm_num)
        (q := 1 - (cell13035 ⟨43,by decide⟩).lower)
        (by norm_num [cell13035]) (by norm_num [cell13035])
      exact ⟨E.1,E.2.trans (by norm_num [cell13035])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy44 (n := 13035) (by norm_num)
        (q := 1 - (cell13035 ⟨44,by decide⟩).lower)
        (by norm_num [cell13035]) (by norm_num [cell13035])
      exact ⟨E.1,E.2.trans (by norm_num [cell13035])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy45 (n := 13035) (by norm_num)
        (q := 1 - (cell13035 ⟨45,by decide⟩).lower)
        (by norm_num [cell13035]) (by norm_num [cell13035])
      exact ⟨E.1,E.2.trans (by norm_num [cell13035])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy46 (n := 13035) (by norm_num)
        (q := 1 - (cell13035 ⟨46,by decide⟩).lower)
        (by norm_num [cell13035]) (by norm_num [cell13035])
      exact ⟨E.1,E.2.trans (by norm_num [cell13035])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy47 (n := 13035) (by norm_num)
        (q := 1 - (cell13035 ⟨47,by decide⟩).lower)
        (by norm_num [cell13035]) (by norm_num [cell13035])
      exact ⟨E.1,E.2.trans (by norm_num [cell13035])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy48 (n := 13035) (by norm_num)
        (q := 1 - (cell13035 ⟨48,by decide⟩).lower)
        (by norm_num [cell13035]) (by norm_num [cell13035])
      exact ⟨E.1,E.2.trans (by norm_num [cell13035])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy49 (n := 13035) (by norm_num)
        (q := 1 - (cell13035 ⟨49,by decide⟩).lower)
        (by norm_num [cell13035]) (by norm_num [cell13035])
      exact ⟨E.1,E.2.trans (by norm_num [cell13035])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy50 (n := 13035) (by norm_num)
        (q := 1 - (cell13035 ⟨50,by decide⟩).lower)
        (by norm_num [cell13035]) (by norm_num [cell13035])
      exact ⟨E.1,E.2.trans (by norm_num [cell13035])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy51 (n := 13035) (by norm_num)
        (q := 1 - (cell13035 ⟨51,by decide⟩).lower)
        (by norm_num [cell13035]) (by norm_num [cell13035])
      exact ⟨E.1,E.2.trans (by norm_num [cell13035])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy52 (n := 13035) (by norm_num)
        (q := 1 - (cell13035 ⟨52,by decide⟩).lower)
        (by norm_num [cell13035]) (by norm_num [cell13035])
      exact ⟨E.1,E.2.trans (by norm_num [cell13035])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13035

/-! Source-cell containment and simple scalar guards at 13035. -/
namespace BstLean.Part269.N13035
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13035)
open BstLean.Part268 (cell13035)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13035 ⟨10,by decide⟩).lower ∧ (cell13035 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13035 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13035 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13035 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13035 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13035 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13035,cell13035,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13035 ⟨11,by decide⟩).lower ∧ (cell13035 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13035 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13035 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13035 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13035 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13035 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13035,cell13035,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13035 ⟨12,by decide⟩).lower ∧ (cell13035 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13035 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13035 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13035 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13035 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13035 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13035,cell13035,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13035 ⟨13,by decide⟩).lower ∧ (cell13035 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13035 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13035 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13035 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13035 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13035 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13035,cell13035,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13035 ⟨14,by decide⟩).lower ∧ (cell13035 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13035 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13035 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13035 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13035 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13035 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13035,cell13035,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13035 ⟨15,by decide⟩).lower ∧ (cell13035 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13035 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13035 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13035 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13035 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13035 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13035,cell13035,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13035 ⟨16,by decide⟩).lower ∧ (cell13035 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13035 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13035 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13035 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13035 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13035 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13035,cell13035,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13035 ⟨17,by decide⟩).lower ∧ (cell13035 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13035 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13035 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13035 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13035 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13035 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13035,cell13035,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13035 ⟨18,by decide⟩).lower ∧ (cell13035 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13035 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13035 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13035 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13035 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13035 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13035,cell13035,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13035 ⟨19,by decide⟩).lower ∧ (cell13035 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13035 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13035 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13035 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13035 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13035 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13035,cell13035,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13035 ⟨20,by decide⟩).lower ∧ (cell13035 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13035 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13035 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13035 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13035 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13035 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13035,cell13035,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13035 ⟨21,by decide⟩).lower ∧ (cell13035 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13035 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13035 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13035 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13035 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13035 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13035,cell13035,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13035 ⟨22,by decide⟩).lower ∧ (cell13035 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13035 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13035 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13035 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13035 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13035 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13035,cell13035,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13035 ⟨23,by decide⟩).lower ∧ (cell13035 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13035 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13035 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13035 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13035 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13035 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13035,cell13035,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13035 ⟨24,by decide⟩).lower ∧ (cell13035 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13035 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13035 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13035 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13035 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13035 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13035,cell13035,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13035 ⟨25,by decide⟩).lower ∧ (cell13035 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13035 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13035 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13035 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13035 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13035 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13035,cell13035,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13035 ⟨26,by decide⟩).lower ∧ (cell13035 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13035 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13035 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13035 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13035 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13035 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13035,cell13035,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13035 ⟨27,by decide⟩).lower ∧ (cell13035 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13035 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13035 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13035 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13035 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13035 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13035,cell13035,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13035 ⟨28,by decide⟩).lower ∧ (cell13035 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13035 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13035 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13035 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13035 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13035 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13035,cell13035,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13035 ⟨29,by decide⟩).lower ∧ (cell13035 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13035 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13035 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13035 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13035 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13035 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13035,cell13035,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13035 ⟨30,by decide⟩).lower ∧ (cell13035 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13035 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13035 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13035 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13035 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13035 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13035,cell13035,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13035 ⟨31,by decide⟩).lower ∧ (cell13035 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13035 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13035 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13035 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13035 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13035 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13035,cell13035,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13035 ⟨32,by decide⟩).lower ∧ (cell13035 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13035 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13035 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13035 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13035 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13035 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13035,cell13035,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13035 ⟨33,by decide⟩).lower ∧ (cell13035 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13035 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13035 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13035 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13035 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13035 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13035,cell13035,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13035 ⟨34,by decide⟩).lower ∧ (cell13035 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13035 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13035 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13035 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13035 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13035 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13035,cell13035,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13035 ⟨35,by decide⟩).lower ∧ (cell13035 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13035 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13035 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13035 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13035 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13035 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13035,cell13035,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13035 ⟨36,by decide⟩).lower ∧ (cell13035 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13035 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13035 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13035 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13035 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13035 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13035,cell13035,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13035 ⟨37,by decide⟩).lower ∧ (cell13035 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13035 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13035 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13035 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13035 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13035 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13035,cell13035,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13035 ⟨38,by decide⟩).lower ∧ (cell13035 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13035 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13035 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13035 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13035 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13035 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13035,cell13035,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13035 ⟨39,by decide⟩).lower ∧ (cell13035 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13035 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13035 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13035 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13035 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13035 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13035,cell13035,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13035 ⟨40,by decide⟩).lower ∧ (cell13035 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13035 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13035 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13035 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13035 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13035 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13035,cell13035,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13035 ⟨41,by decide⟩).lower ∧ (cell13035 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13035 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13035 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13035 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13035 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13035 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13035,cell13035,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13035 ⟨42,by decide⟩).lower ∧ (cell13035 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13035 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13035 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13035 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13035 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13035 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13035,cell13035,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13035 ⟨43,by decide⟩).lower ∧ (cell13035 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13035 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13035 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13035 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13035 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13035 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13035,cell13035,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13035 ⟨44,by decide⟩).lower ∧ (cell13035 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13035 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13035 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13035 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13035 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13035 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13035,cell13035,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13035 ⟨45,by decide⟩).lower ∧ (cell13035 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13035 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13035 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13035 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13035 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13035 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13035,cell13035,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13035 ⟨46,by decide⟩).lower ∧ (cell13035 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13035 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13035 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13035 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13035 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13035 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13035,cell13035,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13035 ⟨47,by decide⟩).lower ∧ (cell13035 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13035 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13035 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13035 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13035 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13035 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13035,cell13035,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13035 ⟨48,by decide⟩).lower ∧ (cell13035 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13035 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13035 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13035 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13035 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13035 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13035,cell13035,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13035 ⟨49,by decide⟩).lower ∧ (cell13035 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13035 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13035 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13035 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13035 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13035 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13035,cell13035,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13035 ⟨50,by decide⟩).lower ∧ (cell13035 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13035 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13035 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13035 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13035 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13035 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13035,cell13035,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13035 ⟨51,by decide⟩).lower ∧ (cell13035 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13035 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13035 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13035 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13035 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13035 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13035,cell13035,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13035 ⟨52,by decide⟩).lower ∧ (cell13035 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13035 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13035 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13035 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13035 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13035 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13035,cell13035,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13035 i).lower ∧
    (cell13035 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13035 i).upper ≤ (0.532 : ℝ) ∧
    (cell13035 i).centre ≤ (0.1 : ℝ) ∧ (cell13035 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13035 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13035 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13035

/-! The local source numeric instances at 13035 have no network premises. -/
namespace BstLean.Part269.N13035
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13035)
open BstLean.Part268 (cell13035)

noncomputable def sourceNumerics13035 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13035 (cell13035 i)
      scalarRow13035.M scalarRow13035.H scalarRow13035.xi := by
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
    energy_allowance := scalarRow13035.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13035]
    centre_nonneg := (scalarRow13035.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D27.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13035])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13035
/-! Actual 13036 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13036
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13036 ≤ (1.035340688497 : ℝ) := by
  have hr : (114.175303809536 : ℝ) ≤ √(13036 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.175303809536 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13036 13036 (11 / 1000) ≤
    (0.008372098891 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13036) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.175303809536 : ℝ) ≤ √(13036 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13036)
  have hdiv : K / √(13036 : ℝ) ≤ K / 114.175303809536 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.175303809536 ≤ (0.008372098891 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13036.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13036 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13036 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13036 := gPlus_lower 13036
end BstLean.Part269.N13036

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13036
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035340688496 : ℝ) ≤ wn 13036 := by
  have hn : √(13036 : ℝ) ≤ 114.175303809537 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13036 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.175303809537 ≤ 2 / √(13036 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000245277698 : ℝ) ≤ rhoBar 13036 BstLean.Part154.csC ∧
    rhoBar 13036 BstLean.Part154.csC ≤ 0.000245278078 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035340688496 : ℝ) / (1.295212 * 13036) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035340688497 : ℝ) / (1.29521 * 13036) := by gcongr
      _ ≤ (0.000245278078 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13036 BstLean.Part154.csC) ≤ 0.000981172474 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13036 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13036 BstLean.Part154.csC) (piBar (rhoBar 13036 BstLean.Part154.csC)) ≤ 0.000187344822 ∧
    cc1 (rhoBar 13036 BstLean.Part154.csC) (piBar (rhoBar 13036 BstLean.Part154.csC)) ≤ 0.000119208801 ∧
    cc2 (rhoBar 13036 BstLean.Part154.csC) ≤ 0.000069201680 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13036 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13036 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13036 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13036 BstLean.Part154.csC * nuR (rhoBar 13036 BstLean.Part154.csC)) ≤ 0.000490571197 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000245278078 : ℝ) * 0.000981172474 := by gcongr
      _ ≤ (0.000490571197 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13036 BstLean.Part154.csC) * nuR (rhoBar 13036 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000981172474 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13036 BstLean.Part154.csC) * rhoBar 13036 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000245278078 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000245278078 / 2 + 0.399 * 0.000981172474 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000187344822 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000490571197 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119208801 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000245278078 / 1.414213562 := by gcongr
      _ ≤ (0.000069201680 : ℝ) := by norm_num

end BstLean.Part269.N13036

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13036
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13036 BstLean.Part154.csC) (piBar (rhoBar 13036 BstLean.Part154.csC)) ≤ 1.51572E-7 := by
  have hr0 : 0 ≤ rhoBar 13036 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13036 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13036 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13036 BstLean.Part154.csC) (piBar (rhoBar 13036 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13036 BstLean.Part154.csC) (piBar (rhoBar 13036 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13036 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000187344822 : ℝ) ^ 2 + 0.000119208801 ^ 2 + 3 * 0.000069201680 ^ 2 +
        2 * 0.797885 * 0.000187344822 * 0.000119208801 + 2 * 0.000187344822 * 0.000069201680 +
        4 * 0.797885 * 0.000119208801 * 0.000069201680 := by gcongr
    _ ≤ (1.51572E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13036 BstLean.Part154.csC Θ ≤ 0.002559199799 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13036 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13036 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13036 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13036 BstLean.Part154.csC) (piBar (rhoBar 13036 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13036 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035340688497 * 1.51572E-7 / (0.000245277698 : ℝ) := by gcongr
    _ ≤ 0.002559199799 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13036 BstLean.Part154.csC Θ ≤ 0.002838284543 + 0.000646669267 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13036 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13036 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13036 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035340688497 : ℝ) * ((2 * Θ * 0.000245278078 +
        (6863 / 10000) * 0.000245278078 * 13036 * 0.000981172474) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002838284543 + 0.000646669267 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13036 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13036 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13036 0.011 Θ ∧ gammaRatio 13036 0.011 Θ ≤ 0.000084320261 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13036 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035340688497 : ℝ) * 0.525 / ((1 - 0.011) * 13036) := by gcongr
      _ ≤ (0.000084320261 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13036 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13036 0.011 Θ) :=
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
    badAllowance 13036 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000383431726 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13036 BstLean.Part154.csC) 1.22 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 2 (rhoBar 13036 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13036 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13036 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13036 0.011 Θ) 1.12 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 1 (gammaRatio 13036 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13036 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13036 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13036 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13036 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035340688497 : ℝ) * 13036 *
        (1.3781E-8 / 1.1045361 + 1.6832E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000383431726 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13036 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003221716269 + 0.003205869066 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13036

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13036
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13036 BstLean.Part154.csC) (piBar (rhoBar 13036 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13036 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13036 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13036 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13036 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13036 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13036 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13036 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13036 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13036 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13036 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13036 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13036 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13036 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13036 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051796225054 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13036) ≤ 0.010459683848 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13036 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035340688497)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010459683848 + 2 * 0.737676 / 13036) := by gcongr
    _ ≤ (0.051796225054 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13036 12 ≤ 0.0015 := by
  exact BstLean.Part269.S27.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13036

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13036
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560518371563 : ℝ) ≤ plow 13036 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13036) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052411397529)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001343579895) : eMP 13036 0.011 xi bn ≤ 0.001157141084 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13036 : ℝ) * (1 - 0.011))) ≤ 0.000572184893 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001343579895 / (13036 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000572184893 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000572184893 : ℝ) + 3.141593 * 0.052411397529 / (13036 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001157141084 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052411397529)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001343579895) : PiBarMP 13036 12 0.011 xi bn ≤ 0.159138672268 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13036 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036654875461 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.545603173350 : ℝ) ≤ √((13036 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.175303809536 : ℝ) ≤ √(13036 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13036) ≤ 0.122026461047 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036654875461 + 0.052411397529 * 1.772454 / (2 * (113.545603173350 : ℝ))) * (1 + 0.001157141084) +
        8 / (13036 * 114.175303809536) + 0.122026461047 := by gcongr
    _ ≤ (0.159138672268 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052411397529)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001343579895) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280731581714) :
    parallelOracle 13036 0.011 xi bn cd ≤ 0.160103442386 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13036 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13036 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560518371563 : ℝ) ≤ plow 13036 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.175303809536 : ℝ) ≤ √(13036 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280731581714 : ℝ) / (2 * 0.560518371563 * 114.175303809536)) * 0.159138672268 +
        0.280731581714 ^ 2 / (2 * 0.560518371563 * 114.175303809536) := by gcongr
    _ ≤ (0.160103442386 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052411397529) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001343579895)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280731581714) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13036 13036 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560518371563 : ℝ) ≤ plow 13036 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.175303809536 : ℝ) ≤ √(13036 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13036 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13036 Θ 1.22 ≤ 0.011614600144 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.175303809536 := by gcongr <;> linarith
      _ ≤ (0.011614600144 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13036 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13036 13036 0.011 ≤ 0.008372098891 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13036 13036 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13036 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13036 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13036 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13036 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160103442386 + 0.011614600144 + (0.008372098891 : ℝ) *
        (1 + 2 * (0.280731581714 + 0.011614600144) / (0.560518371563 * 114.175303809536))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13036]

end BstLean.Part269.N13036

/-! The original eight local profiles supply actual 13036 moment certificates. -/
namespace BstLean.Part269.N13036
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13036 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13036 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13036 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052411397529 ∧
    0 ≤ bN 13036 BstLean.Part154.csC (groupTheta g) ∧ bN 13036 BstLean.Part154.csC (groupTheta g) ≤ 0.001343579895 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13036 13036 0.011
      (momentAllowance 13036 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13036 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13036 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13036 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13036 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13036 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228935356660 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13036 0.011
      (momentAllowance 13036 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13036 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13036
/-! The actual computed-centre upper energy formula at 13036. -/
namespace BstLean.Part269.N13036
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13036

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13036
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13036)
open BstLean.Part268 (cell13036)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084566362278
  | 2 => 0.085493809586
  | 3 => 0.086417280963
  | 4 => 0.087337697346
  | 5 => 0.088256187157
  | 6 => 0.089174118913
  | 7 => 0.090093137247
  | 8 => 0.091015202434
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13036 13036 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13036 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003224237287 + 0.003208677626 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S27.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13036

/-! Actual upper energy certificates on all 43 source endpoints at 13036. -/
namespace BstLean.Part269.N13036
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13036)
open BstLean.Part268 (cell13036)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13036 (gMinus 13036) (1 - (cell13036 i).lower) ≤ 1 ∧
    energyUpper 13036 (gMinus 13036) (BstLean.Part211.gPlus 13036)
      (finiteEnergy 13036 13036 0.011) (1 - (cell13036 i).lower) ≤
      (cell13036 i).energy := by
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
      have E := BstLean.Part269.S27.uniformEnergy10 (n := 13036) (by norm_num)
        (q := 1 - (cell13036 ⟨10,by decide⟩).lower)
        (by norm_num [cell13036]) (by norm_num [cell13036])
      exact ⟨E.1,E.2.trans (by norm_num [cell13036])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy11 (n := 13036) (by norm_num)
        (q := 1 - (cell13036 ⟨11,by decide⟩).lower)
        (by norm_num [cell13036]) (by norm_num [cell13036])
      exact ⟨E.1,E.2.trans (by norm_num [cell13036])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy12 (n := 13036) (by norm_num)
        (q := 1 - (cell13036 ⟨12,by decide⟩).lower)
        (by norm_num [cell13036]) (by norm_num [cell13036])
      exact ⟨E.1,E.2.trans (by norm_num [cell13036])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy13 (n := 13036) (by norm_num)
        (q := 1 - (cell13036 ⟨13,by decide⟩).lower)
        (by norm_num [cell13036]) (by norm_num [cell13036])
      exact ⟨E.1,E.2.trans (by norm_num [cell13036])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy14 (n := 13036) (by norm_num)
        (q := 1 - (cell13036 ⟨14,by decide⟩).lower)
        (by norm_num [cell13036]) (by norm_num [cell13036])
      exact ⟨E.1,E.2.trans (by norm_num [cell13036])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy15 (n := 13036) (by norm_num)
        (q := 1 - (cell13036 ⟨15,by decide⟩).lower)
        (by norm_num [cell13036]) (by norm_num [cell13036])
      exact ⟨E.1,E.2.trans (by norm_num [cell13036])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy16 (n := 13036) (by norm_num)
        (q := 1 - (cell13036 ⟨16,by decide⟩).lower)
        (by norm_num [cell13036]) (by norm_num [cell13036])
      exact ⟨E.1,E.2.trans (by norm_num [cell13036])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy17 (n := 13036) (by norm_num)
        (q := 1 - (cell13036 ⟨17,by decide⟩).lower)
        (by norm_num [cell13036]) (by norm_num [cell13036])
      exact ⟨E.1,E.2.trans (by norm_num [cell13036])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy18 (n := 13036) (by norm_num)
        (q := 1 - (cell13036 ⟨18,by decide⟩).lower)
        (by norm_num [cell13036]) (by norm_num [cell13036])
      exact ⟨E.1,E.2.trans (by norm_num [cell13036])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy19 (n := 13036) (by norm_num)
        (q := 1 - (cell13036 ⟨19,by decide⟩).lower)
        (by norm_num [cell13036]) (by norm_num [cell13036])
      exact ⟨E.1,E.2.trans (by norm_num [cell13036])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy20 (n := 13036) (by norm_num)
        (q := 1 - (cell13036 ⟨20,by decide⟩).lower)
        (by norm_num [cell13036]) (by norm_num [cell13036])
      exact ⟨E.1,E.2.trans (by norm_num [cell13036])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy21 (n := 13036) (by norm_num)
        (q := 1 - (cell13036 ⟨21,by decide⟩).lower)
        (by norm_num [cell13036]) (by norm_num [cell13036])
      exact ⟨E.1,E.2.trans (by norm_num [cell13036])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy22 (n := 13036) (by norm_num)
        (q := 1 - (cell13036 ⟨22,by decide⟩).lower)
        (by norm_num [cell13036]) (by norm_num [cell13036])
      exact ⟨E.1,E.2.trans (by norm_num [cell13036])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy23 (n := 13036) (by norm_num)
        (q := 1 - (cell13036 ⟨23,by decide⟩).lower)
        (by norm_num [cell13036]) (by norm_num [cell13036])
      exact ⟨E.1,E.2.trans (by norm_num [cell13036])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy24 (n := 13036) (by norm_num)
        (q := 1 - (cell13036 ⟨24,by decide⟩).lower)
        (by norm_num [cell13036]) (by norm_num [cell13036])
      exact ⟨E.1,E.2.trans (by norm_num [cell13036])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy25 (n := 13036) (by norm_num)
        (q := 1 - (cell13036 ⟨25,by decide⟩).lower)
        (by norm_num [cell13036]) (by norm_num [cell13036])
      exact ⟨E.1,E.2.trans (by norm_num [cell13036])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy26 (n := 13036) (by norm_num)
        (q := 1 - (cell13036 ⟨26,by decide⟩).lower)
        (by norm_num [cell13036]) (by norm_num [cell13036])
      exact ⟨E.1,E.2.trans (by norm_num [cell13036])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy27 (n := 13036) (by norm_num)
        (q := 1 - (cell13036 ⟨27,by decide⟩).lower)
        (by norm_num [cell13036]) (by norm_num [cell13036])
      exact ⟨E.1,E.2.trans (by norm_num [cell13036])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy28 (n := 13036) (by norm_num)
        (q := 1 - (cell13036 ⟨28,by decide⟩).lower)
        (by norm_num [cell13036]) (by norm_num [cell13036])
      exact ⟨E.1,E.2.trans (by norm_num [cell13036])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy29 (n := 13036) (by norm_num)
        (q := 1 - (cell13036 ⟨29,by decide⟩).lower)
        (by norm_num [cell13036]) (by norm_num [cell13036])
      exact ⟨E.1,E.2.trans (by norm_num [cell13036])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy30 (n := 13036) (by norm_num)
        (q := 1 - (cell13036 ⟨30,by decide⟩).lower)
        (by norm_num [cell13036]) (by norm_num [cell13036])
      exact ⟨E.1,E.2.trans (by norm_num [cell13036])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy31 (n := 13036) (by norm_num)
        (q := 1 - (cell13036 ⟨31,by decide⟩).lower)
        (by norm_num [cell13036]) (by norm_num [cell13036])
      exact ⟨E.1,E.2.trans (by norm_num [cell13036])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy32 (n := 13036) (by norm_num)
        (q := 1 - (cell13036 ⟨32,by decide⟩).lower)
        (by norm_num [cell13036]) (by norm_num [cell13036])
      exact ⟨E.1,E.2.trans (by norm_num [cell13036])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy33 (n := 13036) (by norm_num)
        (q := 1 - (cell13036 ⟨33,by decide⟩).lower)
        (by norm_num [cell13036]) (by norm_num [cell13036])
      exact ⟨E.1,E.2.trans (by norm_num [cell13036])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy34 (n := 13036) (by norm_num)
        (q := 1 - (cell13036 ⟨34,by decide⟩).lower)
        (by norm_num [cell13036]) (by norm_num [cell13036])
      exact ⟨E.1,E.2.trans (by norm_num [cell13036])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy35 (n := 13036) (by norm_num)
        (q := 1 - (cell13036 ⟨35,by decide⟩).lower)
        (by norm_num [cell13036]) (by norm_num [cell13036])
      exact ⟨E.1,E.2.trans (by norm_num [cell13036])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy36 (n := 13036) (by norm_num)
        (q := 1 - (cell13036 ⟨36,by decide⟩).lower)
        (by norm_num [cell13036]) (by norm_num [cell13036])
      exact ⟨E.1,E.2.trans (by norm_num [cell13036])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy37 (n := 13036) (by norm_num)
        (q := 1 - (cell13036 ⟨37,by decide⟩).lower)
        (by norm_num [cell13036]) (by norm_num [cell13036])
      exact ⟨E.1,E.2.trans (by norm_num [cell13036])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy38 (n := 13036) (by norm_num)
        (q := 1 - (cell13036 ⟨38,by decide⟩).lower)
        (by norm_num [cell13036]) (by norm_num [cell13036])
      exact ⟨E.1,E.2.trans (by norm_num [cell13036])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy39 (n := 13036) (by norm_num)
        (q := 1 - (cell13036 ⟨39,by decide⟩).lower)
        (by norm_num [cell13036]) (by norm_num [cell13036])
      exact ⟨E.1,E.2.trans (by norm_num [cell13036])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy40 (n := 13036) (by norm_num)
        (q := 1 - (cell13036 ⟨40,by decide⟩).lower)
        (by norm_num [cell13036]) (by norm_num [cell13036])
      exact ⟨E.1,E.2.trans (by norm_num [cell13036])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy41 (n := 13036) (by norm_num)
        (q := 1 - (cell13036 ⟨41,by decide⟩).lower)
        (by norm_num [cell13036]) (by norm_num [cell13036])
      exact ⟨E.1,E.2.trans (by norm_num [cell13036])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy42 (n := 13036) (by norm_num)
        (q := 1 - (cell13036 ⟨42,by decide⟩).lower)
        (by norm_num [cell13036]) (by norm_num [cell13036])
      exact ⟨E.1,E.2.trans (by norm_num [cell13036])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy43 (n := 13036) (by norm_num)
        (q := 1 - (cell13036 ⟨43,by decide⟩).lower)
        (by norm_num [cell13036]) (by norm_num [cell13036])
      exact ⟨E.1,E.2.trans (by norm_num [cell13036])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy44 (n := 13036) (by norm_num)
        (q := 1 - (cell13036 ⟨44,by decide⟩).lower)
        (by norm_num [cell13036]) (by norm_num [cell13036])
      exact ⟨E.1,E.2.trans (by norm_num [cell13036])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy45 (n := 13036) (by norm_num)
        (q := 1 - (cell13036 ⟨45,by decide⟩).lower)
        (by norm_num [cell13036]) (by norm_num [cell13036])
      exact ⟨E.1,E.2.trans (by norm_num [cell13036])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy46 (n := 13036) (by norm_num)
        (q := 1 - (cell13036 ⟨46,by decide⟩).lower)
        (by norm_num [cell13036]) (by norm_num [cell13036])
      exact ⟨E.1,E.2.trans (by norm_num [cell13036])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy47 (n := 13036) (by norm_num)
        (q := 1 - (cell13036 ⟨47,by decide⟩).lower)
        (by norm_num [cell13036]) (by norm_num [cell13036])
      exact ⟨E.1,E.2.trans (by norm_num [cell13036])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy48 (n := 13036) (by norm_num)
        (q := 1 - (cell13036 ⟨48,by decide⟩).lower)
        (by norm_num [cell13036]) (by norm_num [cell13036])
      exact ⟨E.1,E.2.trans (by norm_num [cell13036])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy49 (n := 13036) (by norm_num)
        (q := 1 - (cell13036 ⟨49,by decide⟩).lower)
        (by norm_num [cell13036]) (by norm_num [cell13036])
      exact ⟨E.1,E.2.trans (by norm_num [cell13036])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy50 (n := 13036) (by norm_num)
        (q := 1 - (cell13036 ⟨50,by decide⟩).lower)
        (by norm_num [cell13036]) (by norm_num [cell13036])
      exact ⟨E.1,E.2.trans (by norm_num [cell13036])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy51 (n := 13036) (by norm_num)
        (q := 1 - (cell13036 ⟨51,by decide⟩).lower)
        (by norm_num [cell13036]) (by norm_num [cell13036])
      exact ⟨E.1,E.2.trans (by norm_num [cell13036])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy52 (n := 13036) (by norm_num)
        (q := 1 - (cell13036 ⟨52,by decide⟩).lower)
        (by norm_num [cell13036]) (by norm_num [cell13036])
      exact ⟨E.1,E.2.trans (by norm_num [cell13036])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13036

/-! Source-cell containment and simple scalar guards at 13036. -/
namespace BstLean.Part269.N13036
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13036)
open BstLean.Part268 (cell13036)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13036 ⟨10,by decide⟩).lower ∧ (cell13036 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13036 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13036 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13036 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13036 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13036 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13036,cell13036,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13036 ⟨11,by decide⟩).lower ∧ (cell13036 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13036 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13036 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13036 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13036 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13036 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13036,cell13036,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13036 ⟨12,by decide⟩).lower ∧ (cell13036 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13036 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13036 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13036 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13036 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13036 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13036,cell13036,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13036 ⟨13,by decide⟩).lower ∧ (cell13036 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13036 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13036 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13036 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13036 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13036 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13036,cell13036,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13036 ⟨14,by decide⟩).lower ∧ (cell13036 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13036 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13036 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13036 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13036 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13036 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13036,cell13036,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13036 ⟨15,by decide⟩).lower ∧ (cell13036 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13036 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13036 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13036 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13036 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13036 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13036,cell13036,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13036 ⟨16,by decide⟩).lower ∧ (cell13036 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13036 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13036 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13036 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13036 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13036 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13036,cell13036,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13036 ⟨17,by decide⟩).lower ∧ (cell13036 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13036 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13036 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13036 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13036 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13036 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13036,cell13036,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13036 ⟨18,by decide⟩).lower ∧ (cell13036 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13036 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13036 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13036 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13036 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13036 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13036,cell13036,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13036 ⟨19,by decide⟩).lower ∧ (cell13036 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13036 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13036 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13036 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13036 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13036 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13036,cell13036,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13036 ⟨20,by decide⟩).lower ∧ (cell13036 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13036 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13036 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13036 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13036 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13036 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13036,cell13036,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13036 ⟨21,by decide⟩).lower ∧ (cell13036 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13036 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13036 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13036 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13036 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13036 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13036,cell13036,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13036 ⟨22,by decide⟩).lower ∧ (cell13036 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13036 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13036 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13036 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13036 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13036 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13036,cell13036,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13036 ⟨23,by decide⟩).lower ∧ (cell13036 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13036 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13036 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13036 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13036 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13036 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13036,cell13036,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13036 ⟨24,by decide⟩).lower ∧ (cell13036 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13036 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13036 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13036 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13036 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13036 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13036,cell13036,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13036 ⟨25,by decide⟩).lower ∧ (cell13036 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13036 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13036 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13036 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13036 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13036 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13036,cell13036,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13036 ⟨26,by decide⟩).lower ∧ (cell13036 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13036 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13036 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13036 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13036 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13036 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13036,cell13036,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13036 ⟨27,by decide⟩).lower ∧ (cell13036 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13036 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13036 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13036 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13036 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13036 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13036,cell13036,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13036 ⟨28,by decide⟩).lower ∧ (cell13036 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13036 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13036 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13036 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13036 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13036 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13036,cell13036,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13036 ⟨29,by decide⟩).lower ∧ (cell13036 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13036 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13036 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13036 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13036 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13036 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13036,cell13036,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13036 ⟨30,by decide⟩).lower ∧ (cell13036 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13036 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13036 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13036 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13036 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13036 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13036,cell13036,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13036 ⟨31,by decide⟩).lower ∧ (cell13036 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13036 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13036 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13036 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13036 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13036 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13036,cell13036,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13036 ⟨32,by decide⟩).lower ∧ (cell13036 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13036 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13036 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13036 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13036 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13036 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13036,cell13036,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13036 ⟨33,by decide⟩).lower ∧ (cell13036 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13036 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13036 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13036 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13036 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13036 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13036,cell13036,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13036 ⟨34,by decide⟩).lower ∧ (cell13036 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13036 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13036 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13036 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13036 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13036 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13036,cell13036,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13036 ⟨35,by decide⟩).lower ∧ (cell13036 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13036 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13036 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13036 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13036 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13036 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13036,cell13036,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13036 ⟨36,by decide⟩).lower ∧ (cell13036 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13036 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13036 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13036 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13036 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13036 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13036,cell13036,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13036 ⟨37,by decide⟩).lower ∧ (cell13036 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13036 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13036 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13036 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13036 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13036 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13036,cell13036,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13036 ⟨38,by decide⟩).lower ∧ (cell13036 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13036 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13036 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13036 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13036 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13036 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13036,cell13036,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13036 ⟨39,by decide⟩).lower ∧ (cell13036 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13036 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13036 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13036 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13036 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13036 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13036,cell13036,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13036 ⟨40,by decide⟩).lower ∧ (cell13036 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13036 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13036 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13036 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13036 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13036 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13036,cell13036,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13036 ⟨41,by decide⟩).lower ∧ (cell13036 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13036 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13036 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13036 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13036 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13036 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13036,cell13036,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13036 ⟨42,by decide⟩).lower ∧ (cell13036 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13036 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13036 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13036 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13036 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13036 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13036,cell13036,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13036 ⟨43,by decide⟩).lower ∧ (cell13036 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13036 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13036 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13036 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13036 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13036 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13036,cell13036,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13036 ⟨44,by decide⟩).lower ∧ (cell13036 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13036 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13036 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13036 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13036 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13036 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13036,cell13036,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13036 ⟨45,by decide⟩).lower ∧ (cell13036 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13036 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13036 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13036 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13036 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13036 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13036,cell13036,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13036 ⟨46,by decide⟩).lower ∧ (cell13036 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13036 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13036 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13036 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13036 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13036 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13036,cell13036,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13036 ⟨47,by decide⟩).lower ∧ (cell13036 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13036 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13036 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13036 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13036 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13036 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13036,cell13036,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13036 ⟨48,by decide⟩).lower ∧ (cell13036 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13036 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13036 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13036 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13036 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13036 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13036,cell13036,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13036 ⟨49,by decide⟩).lower ∧ (cell13036 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13036 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13036 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13036 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13036 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13036 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13036,cell13036,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13036 ⟨50,by decide⟩).lower ∧ (cell13036 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13036 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13036 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13036 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13036 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13036 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13036,cell13036,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13036 ⟨51,by decide⟩).lower ∧ (cell13036 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13036 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13036 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13036 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13036 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13036 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13036,cell13036,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13036 ⟨52,by decide⟩).lower ∧ (cell13036 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13036 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13036 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13036 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13036 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13036 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13036,cell13036,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13036 i).lower ∧
    (cell13036 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13036 i).upper ≤ (0.532 : ℝ) ∧
    (cell13036 i).centre ≤ (0.1 : ℝ) ∧ (cell13036 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13036 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13036 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13036

/-! The local source numeric instances at 13036 have no network premises. -/
namespace BstLean.Part269.N13036
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13036)
open BstLean.Part268 (cell13036)

noncomputable def sourceNumerics13036 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13036 (cell13036 i)
      scalarRow13036.M scalarRow13036.H scalarRow13036.xi := by
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
    energy_allowance := scalarRow13036.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13036]
    centre_nonneg := (scalarRow13036.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D27.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13036])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13036
/-! Actual 13037 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13037
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13037 ≤ (1.035339321303 : ℝ) := by
  have hr : (114.179682956294 : ℝ) ≤ √(13037 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.179682956294 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13037 13037 (11 / 1000) ≤
    (0.008371777792 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13037) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.179682956294 : ℝ) ≤ √(13037 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13037)
  have hdiv : K / √(13037 : ℝ) ≤ K / 114.179682956294 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.179682956294 ≤ (0.008371777792 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13037.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13037 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13037 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13037 := gPlus_lower 13037
end BstLean.Part269.N13037

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13037
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035339321302 : ℝ) ≤ wn 13037 := by
  have hn : √(13037 : ℝ) ≤ 114.179682956295 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13037 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.179682956295 ≤ 2 / √(13037 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000245258560 : ℝ) ≤ rhoBar 13037 BstLean.Part154.csC ∧
    rhoBar 13037 BstLean.Part154.csC ≤ 0.000245258940 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035339321302 : ℝ) / (1.295212 * 13037) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035339321303 : ℝ) / (1.29521 * 13037) := by gcongr
      _ ≤ (0.000245258940 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13037 BstLean.Part154.csC) ≤ 0.000981095912 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13037 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13037 BstLean.Part154.csC) (piBar (rhoBar 13037 BstLean.Part154.csC)) ≤ 0.000187330204 ∧
    cc1 (rhoBar 13037 BstLean.Part154.csC) (piBar (rhoBar 13037 BstLean.Part154.csC)) ≤ 0.000119199500 ∧
    cc2 (rhoBar 13037 BstLean.Part154.csC) ≤ 0.000069196280 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13037 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13037 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13037 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13037 BstLean.Part154.csC * nuR (rhoBar 13037 BstLean.Part154.csC)) ≤ 0.000490532918 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000245258940 : ℝ) * 0.000981095912 := by gcongr
      _ ≤ (0.000490532918 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13037 BstLean.Part154.csC) * nuR (rhoBar 13037 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000981095912 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13037 BstLean.Part154.csC) * rhoBar 13037 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000245258940 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000245258940 / 2 + 0.399 * 0.000981095912 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000187330204 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000490532918 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119199500 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000245258940 / 1.414213562 := by gcongr
      _ ≤ (0.000069196280 : ℝ) := by norm_num

end BstLean.Part269.N13037

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13037
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13037 BstLean.Part154.csC) (piBar (rhoBar 13037 BstLean.Part154.csC)) ≤ 1.51548E-7 := by
  have hr0 : 0 ≤ rhoBar 13037 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13037 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13037 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13037 BstLean.Part154.csC) (piBar (rhoBar 13037 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13037 BstLean.Part154.csC) (piBar (rhoBar 13037 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13037 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000187330204 : ℝ) ^ 2 + 0.000119199500 ^ 2 + 3 * 0.000069196280 ^ 2 +
        2 * 0.797885 * 0.000187330204 * 0.000119199500 + 2 * 0.000187330204 * 0.000069196280 +
        4 * 0.797885 * 0.000119199500 * 0.000069196280 := by gcongr
    _ ≤ (1.51548E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13037 BstLean.Part154.csC Θ ≤ 0.002558990862 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13037 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13037 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13037 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13037 BstLean.Part154.csC) (piBar (rhoBar 13037 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13037 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035339321303 * 1.51548E-7 / (0.000245258560 : ℝ) := by gcongr
    _ ≤ 0.002558990862 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13037 BstLean.Part154.csC Θ ≤ 0.002838055571 + 0.000646617956 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13037 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13037 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13037 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035339321303 : ℝ) * ((2 * Θ * 0.000245258940 +
        (6863 / 10000) * 0.000245258940 * 13037 * 0.000981095912) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002838055571 + 0.000646617956 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13037 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13037 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13037 0.011 Θ ∧ gammaRatio 13037 0.011 Θ ≤ 0.000084313682 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13037 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035339321303 : ℝ) * 0.525 / ((1 - 0.011) * 13037) := by gcongr
      _ ≤ (0.000084313682 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13037 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13037 0.011 Θ) :=
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
    badAllowance 13037 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000383431726 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13037 BstLean.Part154.csC) 1.22 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 2 (rhoBar 13037 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13037 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13037 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13037 0.011 Θ) 1.12 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 1 (gammaRatio 13037 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13037 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13037 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13037 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13037 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035339321303 : ℝ) * 13037 *
        (1.3781E-8 / 1.1045361 + 1.6832E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000383431726 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13037 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003221487297 + 0.003205608818 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13037

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13037
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13037 BstLean.Part154.csC) (piBar (rhoBar 13037 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13037 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13037 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13037 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13037 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13037 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13037 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13037 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13037 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13037 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13037 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13037 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13037 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13037 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13037 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051794217246 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13037) ≤ 0.010459282687 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13037 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035339321303)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010459282687 + 2 * 0.737676 / 13037) := by gcongr
    _ ≤ (0.051794217246 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13037 12 ≤ 0.0015 := by
  exact BstLean.Part269.S27.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13037

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13037
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560518414481 : ℝ) ≤ plow 13037 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13037) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052411031927)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001343470203) : eMP 13037 0.011 xi bn ≤ 0.001157049411 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13037 : ℝ) * (1 - 0.011))) ≤ 0.000572139591 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001343470203 / (13037 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000572139591 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000572139591 : ℝ) + 3.141593 * 0.052411031927 / (13037 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001157049411 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052411031927)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001343470203) : PiBarMP 13037 12 0.011 xi bn ≤ 0.159132471549 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13037 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036653379149 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.549958168200 : ℝ) ≤ √((13037 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.179682956294 : ℝ) ≤ √(13037 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13037) ≤ 0.122021780952 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036653379149 + 0.052411031927 * 1.772454 / (2 * (113.549958168200 : ℝ))) * (1 + 0.001157049411) +
        8 / (13037 * 114.179682956294) + 0.122021780952 := by gcongr
    _ ≤ (0.159132471549 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052411031927)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001343470203) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280728775422) :
    parallelOracle 13037 0.011 xi bn cd ≤ 0.160097175194 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13037 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13037 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560518414481 : ℝ) ≤ plow 13037 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.179682956294 : ℝ) ≤ √(13037 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280728775422 : ℝ) / (2 * 0.560518414481 * 114.179682956294)) * 0.159132471549 +
        0.280728775422 ^ 2 / (2 * 0.560518414481 * 114.179682956294) := by gcongr
    _ ≤ (0.160097175194 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052411031927) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001343470203)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280728775422) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13037 13037 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560518414481 : ℝ) ≤ plow 13037 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.179682956294 : ℝ) ≤ √(13037 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13037 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13037 Θ 1.22 ≤ 0.011614154688 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.179682956294 := by gcongr <;> linarith
      _ ≤ (0.011614154688 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13037 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13037 13037 0.011 ≤ 0.008371777792 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13037 13037 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13037 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13037 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13037 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13037 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160097175194 + 0.011614154688 + (0.008371777792 : ℝ) *
        (1 + 2 * (0.280728775422 + 0.011614154688) / (0.560518414481 * 114.179682956294))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13037]

end BstLean.Part269.N13037

/-! The original eight local profiles supply actual 13037 moment certificates. -/
namespace BstLean.Part269.N13037
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13037 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13037 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13037 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052411031927 ∧
    0 ≤ bN 13037 BstLean.Part154.csC (groupTheta g) ∧ bN 13037 BstLean.Part154.csC (groupTheta g) ≤ 0.001343470203 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13037 13037 0.011
      (momentAllowance 13037 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13037 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13037 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13037 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13037 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13037 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228934558176 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13037 0.011
      (momentAllowance 13037 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13037 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13037
/-! The actual computed-centre upper energy formula at 13037. -/
namespace BstLean.Part269.N13037
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13037

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13037
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13037)
open BstLean.Part268 (cell13037)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084563772650
  | 2 => 0.085491186413
  | 3 => 0.086414619231
  | 4 => 0.087334990861
  | 5 => 0.088253428327
  | 6 => 0.089171298505
  | 7 => 0.090090244110
  | 8 => 0.091012223194
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13037 13037 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13037 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003224237287 + 0.003208677626 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S27.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S27.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13037

/-! Actual upper energy certificates on all 43 source endpoints at 13037. -/
namespace BstLean.Part269.N13037
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13037)
open BstLean.Part268 (cell13037)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13037 (gMinus 13037) (1 - (cell13037 i).lower) ≤ 1 ∧
    energyUpper 13037 (gMinus 13037) (BstLean.Part211.gPlus 13037)
      (finiteEnergy 13037 13037 0.011) (1 - (cell13037 i).lower) ≤
      (cell13037 i).energy := by
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
      have E := BstLean.Part269.S27.uniformEnergy10 (n := 13037) (by norm_num)
        (q := 1 - (cell13037 ⟨10,by decide⟩).lower)
        (by norm_num [cell13037]) (by norm_num [cell13037])
      exact ⟨E.1,E.2.trans (by norm_num [cell13037])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy11 (n := 13037) (by norm_num)
        (q := 1 - (cell13037 ⟨11,by decide⟩).lower)
        (by norm_num [cell13037]) (by norm_num [cell13037])
      exact ⟨E.1,E.2.trans (by norm_num [cell13037])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy12 (n := 13037) (by norm_num)
        (q := 1 - (cell13037 ⟨12,by decide⟩).lower)
        (by norm_num [cell13037]) (by norm_num [cell13037])
      exact ⟨E.1,E.2.trans (by norm_num [cell13037])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy13 (n := 13037) (by norm_num)
        (q := 1 - (cell13037 ⟨13,by decide⟩).lower)
        (by norm_num [cell13037]) (by norm_num [cell13037])
      exact ⟨E.1,E.2.trans (by norm_num [cell13037])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy14 (n := 13037) (by norm_num)
        (q := 1 - (cell13037 ⟨14,by decide⟩).lower)
        (by norm_num [cell13037]) (by norm_num [cell13037])
      exact ⟨E.1,E.2.trans (by norm_num [cell13037])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy15 (n := 13037) (by norm_num)
        (q := 1 - (cell13037 ⟨15,by decide⟩).lower)
        (by norm_num [cell13037]) (by norm_num [cell13037])
      exact ⟨E.1,E.2.trans (by norm_num [cell13037])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy16 (n := 13037) (by norm_num)
        (q := 1 - (cell13037 ⟨16,by decide⟩).lower)
        (by norm_num [cell13037]) (by norm_num [cell13037])
      exact ⟨E.1,E.2.trans (by norm_num [cell13037])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy17 (n := 13037) (by norm_num)
        (q := 1 - (cell13037 ⟨17,by decide⟩).lower)
        (by norm_num [cell13037]) (by norm_num [cell13037])
      exact ⟨E.1,E.2.trans (by norm_num [cell13037])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy18 (n := 13037) (by norm_num)
        (q := 1 - (cell13037 ⟨18,by decide⟩).lower)
        (by norm_num [cell13037]) (by norm_num [cell13037])
      exact ⟨E.1,E.2.trans (by norm_num [cell13037])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy19 (n := 13037) (by norm_num)
        (q := 1 - (cell13037 ⟨19,by decide⟩).lower)
        (by norm_num [cell13037]) (by norm_num [cell13037])
      exact ⟨E.1,E.2.trans (by norm_num [cell13037])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy20 (n := 13037) (by norm_num)
        (q := 1 - (cell13037 ⟨20,by decide⟩).lower)
        (by norm_num [cell13037]) (by norm_num [cell13037])
      exact ⟨E.1,E.2.trans (by norm_num [cell13037])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy21 (n := 13037) (by norm_num)
        (q := 1 - (cell13037 ⟨21,by decide⟩).lower)
        (by norm_num [cell13037]) (by norm_num [cell13037])
      exact ⟨E.1,E.2.trans (by norm_num [cell13037])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy22 (n := 13037) (by norm_num)
        (q := 1 - (cell13037 ⟨22,by decide⟩).lower)
        (by norm_num [cell13037]) (by norm_num [cell13037])
      exact ⟨E.1,E.2.trans (by norm_num [cell13037])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy23 (n := 13037) (by norm_num)
        (q := 1 - (cell13037 ⟨23,by decide⟩).lower)
        (by norm_num [cell13037]) (by norm_num [cell13037])
      exact ⟨E.1,E.2.trans (by norm_num [cell13037])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy24 (n := 13037) (by norm_num)
        (q := 1 - (cell13037 ⟨24,by decide⟩).lower)
        (by norm_num [cell13037]) (by norm_num [cell13037])
      exact ⟨E.1,E.2.trans (by norm_num [cell13037])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy25 (n := 13037) (by norm_num)
        (q := 1 - (cell13037 ⟨25,by decide⟩).lower)
        (by norm_num [cell13037]) (by norm_num [cell13037])
      exact ⟨E.1,E.2.trans (by norm_num [cell13037])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy26 (n := 13037) (by norm_num)
        (q := 1 - (cell13037 ⟨26,by decide⟩).lower)
        (by norm_num [cell13037]) (by norm_num [cell13037])
      exact ⟨E.1,E.2.trans (by norm_num [cell13037])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy27 (n := 13037) (by norm_num)
        (q := 1 - (cell13037 ⟨27,by decide⟩).lower)
        (by norm_num [cell13037]) (by norm_num [cell13037])
      exact ⟨E.1,E.2.trans (by norm_num [cell13037])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy28 (n := 13037) (by norm_num)
        (q := 1 - (cell13037 ⟨28,by decide⟩).lower)
        (by norm_num [cell13037]) (by norm_num [cell13037])
      exact ⟨E.1,E.2.trans (by norm_num [cell13037])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy29 (n := 13037) (by norm_num)
        (q := 1 - (cell13037 ⟨29,by decide⟩).lower)
        (by norm_num [cell13037]) (by norm_num [cell13037])
      exact ⟨E.1,E.2.trans (by norm_num [cell13037])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy30 (n := 13037) (by norm_num)
        (q := 1 - (cell13037 ⟨30,by decide⟩).lower)
        (by norm_num [cell13037]) (by norm_num [cell13037])
      exact ⟨E.1,E.2.trans (by norm_num [cell13037])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy31 (n := 13037) (by norm_num)
        (q := 1 - (cell13037 ⟨31,by decide⟩).lower)
        (by norm_num [cell13037]) (by norm_num [cell13037])
      exact ⟨E.1,E.2.trans (by norm_num [cell13037])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy32 (n := 13037) (by norm_num)
        (q := 1 - (cell13037 ⟨32,by decide⟩).lower)
        (by norm_num [cell13037]) (by norm_num [cell13037])
      exact ⟨E.1,E.2.trans (by norm_num [cell13037])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy33 (n := 13037) (by norm_num)
        (q := 1 - (cell13037 ⟨33,by decide⟩).lower)
        (by norm_num [cell13037]) (by norm_num [cell13037])
      exact ⟨E.1,E.2.trans (by norm_num [cell13037])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy34 (n := 13037) (by norm_num)
        (q := 1 - (cell13037 ⟨34,by decide⟩).lower)
        (by norm_num [cell13037]) (by norm_num [cell13037])
      exact ⟨E.1,E.2.trans (by norm_num [cell13037])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy35 (n := 13037) (by norm_num)
        (q := 1 - (cell13037 ⟨35,by decide⟩).lower)
        (by norm_num [cell13037]) (by norm_num [cell13037])
      exact ⟨E.1,E.2.trans (by norm_num [cell13037])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy36 (n := 13037) (by norm_num)
        (q := 1 - (cell13037 ⟨36,by decide⟩).lower)
        (by norm_num [cell13037]) (by norm_num [cell13037])
      exact ⟨E.1,E.2.trans (by norm_num [cell13037])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy37 (n := 13037) (by norm_num)
        (q := 1 - (cell13037 ⟨37,by decide⟩).lower)
        (by norm_num [cell13037]) (by norm_num [cell13037])
      exact ⟨E.1,E.2.trans (by norm_num [cell13037])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy38 (n := 13037) (by norm_num)
        (q := 1 - (cell13037 ⟨38,by decide⟩).lower)
        (by norm_num [cell13037]) (by norm_num [cell13037])
      exact ⟨E.1,E.2.trans (by norm_num [cell13037])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy39 (n := 13037) (by norm_num)
        (q := 1 - (cell13037 ⟨39,by decide⟩).lower)
        (by norm_num [cell13037]) (by norm_num [cell13037])
      exact ⟨E.1,E.2.trans (by norm_num [cell13037])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy40 (n := 13037) (by norm_num)
        (q := 1 - (cell13037 ⟨40,by decide⟩).lower)
        (by norm_num [cell13037]) (by norm_num [cell13037])
      exact ⟨E.1,E.2.trans (by norm_num [cell13037])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy41 (n := 13037) (by norm_num)
        (q := 1 - (cell13037 ⟨41,by decide⟩).lower)
        (by norm_num [cell13037]) (by norm_num [cell13037])
      exact ⟨E.1,E.2.trans (by norm_num [cell13037])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy42 (n := 13037) (by norm_num)
        (q := 1 - (cell13037 ⟨42,by decide⟩).lower)
        (by norm_num [cell13037]) (by norm_num [cell13037])
      exact ⟨E.1,E.2.trans (by norm_num [cell13037])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy43 (n := 13037) (by norm_num)
        (q := 1 - (cell13037 ⟨43,by decide⟩).lower)
        (by norm_num [cell13037]) (by norm_num [cell13037])
      exact ⟨E.1,E.2.trans (by norm_num [cell13037])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy44 (n := 13037) (by norm_num)
        (q := 1 - (cell13037 ⟨44,by decide⟩).lower)
        (by norm_num [cell13037]) (by norm_num [cell13037])
      exact ⟨E.1,E.2.trans (by norm_num [cell13037])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy45 (n := 13037) (by norm_num)
        (q := 1 - (cell13037 ⟨45,by decide⟩).lower)
        (by norm_num [cell13037]) (by norm_num [cell13037])
      exact ⟨E.1,E.2.trans (by norm_num [cell13037])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy46 (n := 13037) (by norm_num)
        (q := 1 - (cell13037 ⟨46,by decide⟩).lower)
        (by norm_num [cell13037]) (by norm_num [cell13037])
      exact ⟨E.1,E.2.trans (by norm_num [cell13037])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy47 (n := 13037) (by norm_num)
        (q := 1 - (cell13037 ⟨47,by decide⟩).lower)
        (by norm_num [cell13037]) (by norm_num [cell13037])
      exact ⟨E.1,E.2.trans (by norm_num [cell13037])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy48 (n := 13037) (by norm_num)
        (q := 1 - (cell13037 ⟨48,by decide⟩).lower)
        (by norm_num [cell13037]) (by norm_num [cell13037])
      exact ⟨E.1,E.2.trans (by norm_num [cell13037])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy49 (n := 13037) (by norm_num)
        (q := 1 - (cell13037 ⟨49,by decide⟩).lower)
        (by norm_num [cell13037]) (by norm_num [cell13037])
      exact ⟨E.1,E.2.trans (by norm_num [cell13037])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy50 (n := 13037) (by norm_num)
        (q := 1 - (cell13037 ⟨50,by decide⟩).lower)
        (by norm_num [cell13037]) (by norm_num [cell13037])
      exact ⟨E.1,E.2.trans (by norm_num [cell13037])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy51 (n := 13037) (by norm_num)
        (q := 1 - (cell13037 ⟨51,by decide⟩).lower)
        (by norm_num [cell13037]) (by norm_num [cell13037])
      exact ⟨E.1,E.2.trans (by norm_num [cell13037])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy52 (n := 13037) (by norm_num)
        (q := 1 - (cell13037 ⟨52,by decide⟩).lower)
        (by norm_num [cell13037]) (by norm_num [cell13037])
      exact ⟨E.1,E.2.trans (by norm_num [cell13037])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13037

/-! Source-cell containment and simple scalar guards at 13037. -/
namespace BstLean.Part269.N13037
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13037)
open BstLean.Part268 (cell13037)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13037 ⟨10,by decide⟩).lower ∧ (cell13037 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13037 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13037 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13037 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13037 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13037 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13037,cell13037,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13037 ⟨11,by decide⟩).lower ∧ (cell13037 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13037 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13037 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13037 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13037 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13037 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13037,cell13037,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13037 ⟨12,by decide⟩).lower ∧ (cell13037 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13037 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13037 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13037 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13037 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13037 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13037,cell13037,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13037 ⟨13,by decide⟩).lower ∧ (cell13037 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13037 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13037 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13037 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13037 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13037 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13037,cell13037,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13037 ⟨14,by decide⟩).lower ∧ (cell13037 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13037 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13037 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13037 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13037 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13037 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13037,cell13037,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13037 ⟨15,by decide⟩).lower ∧ (cell13037 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13037 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13037 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13037 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13037 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13037 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13037,cell13037,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13037 ⟨16,by decide⟩).lower ∧ (cell13037 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13037 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13037 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13037 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13037 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13037 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13037,cell13037,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13037 ⟨17,by decide⟩).lower ∧ (cell13037 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13037 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13037 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13037 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13037 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13037 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13037,cell13037,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13037 ⟨18,by decide⟩).lower ∧ (cell13037 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13037 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13037 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13037 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13037 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13037 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13037,cell13037,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13037 ⟨19,by decide⟩).lower ∧ (cell13037 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13037 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13037 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13037 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13037 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13037 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13037,cell13037,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13037 ⟨20,by decide⟩).lower ∧ (cell13037 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13037 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13037 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13037 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13037 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13037 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13037,cell13037,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13037 ⟨21,by decide⟩).lower ∧ (cell13037 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13037 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13037 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13037 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13037 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13037 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13037,cell13037,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13037 ⟨22,by decide⟩).lower ∧ (cell13037 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13037 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13037 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13037 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13037 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13037 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13037,cell13037,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13037 ⟨23,by decide⟩).lower ∧ (cell13037 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13037 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13037 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13037 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13037 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13037 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13037,cell13037,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13037 ⟨24,by decide⟩).lower ∧ (cell13037 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13037 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13037 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13037 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13037 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13037 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13037,cell13037,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13037 ⟨25,by decide⟩).lower ∧ (cell13037 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13037 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13037 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13037 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13037 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13037 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13037,cell13037,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13037 ⟨26,by decide⟩).lower ∧ (cell13037 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13037 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13037 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13037 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13037 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13037 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13037,cell13037,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13037 ⟨27,by decide⟩).lower ∧ (cell13037 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13037 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13037 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13037 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13037 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13037 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13037,cell13037,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13037 ⟨28,by decide⟩).lower ∧ (cell13037 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13037 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13037 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13037 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13037 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13037 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13037,cell13037,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13037 ⟨29,by decide⟩).lower ∧ (cell13037 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13037 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13037 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13037 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13037 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13037 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13037,cell13037,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13037 ⟨30,by decide⟩).lower ∧ (cell13037 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13037 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13037 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13037 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13037 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13037 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13037,cell13037,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13037 ⟨31,by decide⟩).lower ∧ (cell13037 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13037 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13037 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13037 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13037 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13037 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13037,cell13037,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13037 ⟨32,by decide⟩).lower ∧ (cell13037 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13037 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13037 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13037 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13037 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13037 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13037,cell13037,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13037 ⟨33,by decide⟩).lower ∧ (cell13037 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13037 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13037 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13037 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13037 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13037 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13037,cell13037,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13037 ⟨34,by decide⟩).lower ∧ (cell13037 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13037 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13037 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13037 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13037 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13037 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13037,cell13037,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13037 ⟨35,by decide⟩).lower ∧ (cell13037 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13037 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13037 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13037 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13037 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13037 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13037,cell13037,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13037 ⟨36,by decide⟩).lower ∧ (cell13037 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13037 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13037 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13037 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13037 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13037 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13037,cell13037,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13037 ⟨37,by decide⟩).lower ∧ (cell13037 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13037 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13037 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13037 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13037 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13037 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13037,cell13037,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13037 ⟨38,by decide⟩).lower ∧ (cell13037 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13037 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13037 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13037 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13037 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13037 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13037,cell13037,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13037 ⟨39,by decide⟩).lower ∧ (cell13037 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13037 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13037 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13037 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13037 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13037 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13037,cell13037,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13037 ⟨40,by decide⟩).lower ∧ (cell13037 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13037 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13037 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13037 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13037 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13037 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13037,cell13037,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13037 ⟨41,by decide⟩).lower ∧ (cell13037 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13037 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13037 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13037 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13037 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13037 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13037,cell13037,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13037 ⟨42,by decide⟩).lower ∧ (cell13037 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13037 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13037 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13037 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13037 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13037 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13037,cell13037,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13037 ⟨43,by decide⟩).lower ∧ (cell13037 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13037 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13037 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13037 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13037 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13037 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13037,cell13037,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13037 ⟨44,by decide⟩).lower ∧ (cell13037 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13037 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13037 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13037 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13037 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13037 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13037,cell13037,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13037 ⟨45,by decide⟩).lower ∧ (cell13037 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13037 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13037 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13037 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13037 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13037 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13037,cell13037,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13037 ⟨46,by decide⟩).lower ∧ (cell13037 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13037 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13037 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13037 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13037 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13037 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13037,cell13037,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13037 ⟨47,by decide⟩).lower ∧ (cell13037 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13037 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13037 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13037 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13037 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13037 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13037,cell13037,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13037 ⟨48,by decide⟩).lower ∧ (cell13037 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13037 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13037 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13037 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13037 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13037 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13037,cell13037,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13037 ⟨49,by decide⟩).lower ∧ (cell13037 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13037 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13037 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13037 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13037 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13037 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13037,cell13037,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13037 ⟨50,by decide⟩).lower ∧ (cell13037 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13037 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13037 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13037 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13037 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13037 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13037,cell13037,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13037 ⟨51,by decide⟩).lower ∧ (cell13037 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13037 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13037 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13037 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13037 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13037 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13037,cell13037,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13037 ⟨52,by decide⟩).lower ∧ (cell13037 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13037 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13037 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13037 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13037 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13037 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13037,cell13037,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13037 i).lower ∧
    (cell13037 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13037 i).upper ≤ (0.532 : ℝ) ∧
    (cell13037 i).centre ≤ (0.1 : ℝ) ∧ (cell13037 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13037 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13037 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13037

/-! The local source numeric instances at 13037 have no network premises. -/
namespace BstLean.Part269.N13037
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13037)
open BstLean.Part268 (cell13037)

noncomputable def sourceNumerics13037 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13037 (cell13037 i)
      scalarRow13037.M scalarRow13037.H scalarRow13037.xi := by
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
    energy_allowance := scalarRow13037.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13037]
    centre_nonneg := (scalarRow13037.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D27.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13037])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13037