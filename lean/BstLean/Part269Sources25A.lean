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
import BstLean.Part269Direction25
import BstLean.Part269Shared25
import BstLean.Part269Finite
import BstLean.Part269Rows25
import BstLean.Part269Source
/-! Actual 12975 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12975
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12975 ≤ (1.035424387669 : ℝ) := by
  have hr : (113.907857498945 : ℝ) ≤ √(12975 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.907857498945 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12975 12975 (11 / 1000) ≤
    (0.008391756041 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12975) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.907857498945 : ℝ) ≤ √(12975 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12975)
  have hdiv : K / √(12975 : ℝ) ≤ K / 113.907857498945 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.907857498945 ≤ (0.008391756041 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12975.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12975 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12975 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12975 := gPlus_lower 12975
end BstLean.Part269.N12975

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12975
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035424387668 : ℝ) ≤ wn 12975 := by
  have hn : √(12975 : ℝ) ≤ 113.907857498946 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12975 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.907857498946 ≤ 2 / √(12975 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000246450756 : ℝ) ≤ rhoBar 12975 BstLean.Part154.csC ∧
    rhoBar 12975 BstLean.Part154.csC ≤ 0.000246451137 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035424387668 : ℝ) / (1.295212 * 12975) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035424387669 : ℝ) / (1.29521 * 12975) := by gcongr
      _ ≤ (0.000246451137 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12975 BstLean.Part154.csC) ≤ 0.000985865287 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12975 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12975 BstLean.Part154.csC) (piBar (rhoBar 12975 BstLean.Part154.csC)) ≤ 0.000188240852 ∧
    cc1 (rhoBar 12975 BstLean.Part154.csC) (piBar (rhoBar 12975 BstLean.Part154.csC)) ≤ 0.000119778943 ∧
    cc2 (rhoBar 12975 BstLean.Part154.csC) ≤ 0.000069532641 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12975 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12975 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12975 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12975 BstLean.Part154.csC * nuR (rhoBar 12975 BstLean.Part154.csC)) ≤ 0.000492917459 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000246451137 : ℝ) * 0.000985865287 := by gcongr
      _ ≤ (0.000492917459 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12975 BstLean.Part154.csC) * nuR (rhoBar 12975 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000985865287 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12975 BstLean.Part154.csC) * rhoBar 12975 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000246451137 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000246451137 / 2 + 0.399 * 0.000985865287 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000188240852 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000492917459 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119778943 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000246451137 / 1.414213562 := by gcongr
      _ ≤ (0.000069532641 : ℝ) := by norm_num

end BstLean.Part269.N12975

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12975
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12975 BstLean.Part154.csC) (piBar (rhoBar 12975 BstLean.Part154.csC)) ≤ 1.53025E-7 := by
  have hr0 : 0 ≤ rhoBar 12975 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12975 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12975 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12975 BstLean.Part154.csC) (piBar (rhoBar 12975 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12975 BstLean.Part154.csC) (piBar (rhoBar 12975 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12975 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000188240852 : ℝ) ^ 2 + 0.000119778943 ^ 2 + 3 * 0.000069532641 ^ 2 +
        2 * 0.797885 * 0.000188240852 * 0.000119778943 + 2 * 0.000188240852 * 0.000069532641 +
        4 * 0.797885 * 0.000119778943 * 0.000069532641 := by gcongr
    _ ≤ (1.53025E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12975 BstLean.Part154.csC Θ ≤ 0.002571642620 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12975 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12975 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12975 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12975 BstLean.Part154.csC) (piBar (rhoBar 12975 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12975 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035424387669 * 1.53025E-7 / (0.000246450756 : ℝ) := by gcongr
    _ ≤ 0.002571642620 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12975 BstLean.Part154.csC Θ ≤ 0.002852320777 + 0.000649814534 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12975 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12975 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12975 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035424387669 : ℝ) * ((2 * Θ * 0.000246451137 +
        (6863 / 10000) * 0.000246451137 * 12975 * 0.000985865287) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002852320777 + 0.000649814534 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12975 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12975 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12975 0.011 Θ ∧ gammaRatio 12975 0.011 Θ ≤ 0.000084723528 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12975 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035424387669 : ℝ) * 0.525 / ((1 - 0.011) * 12975) := by gcongr
      _ ≤ (0.000084723528 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12975 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12975 0.011 Θ) :=
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
    badAllowance 12975 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000421835223 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12975 BstLean.Part154.csC) 1.22 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 2 (rhoBar 12975 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12975 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12975 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12975 0.011 Θ) 1.12 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 1 (gammaRatio 12975 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12975 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12975 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12975 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12975 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035424387669 : ℝ) * 12975 *
        (1.5230E-8 / 1.1045361 + 1.8602E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000421835223 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12975 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003274156000 + 0.003221457154 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12975

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12975
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12975 BstLean.Part154.csC) (piBar (rhoBar 12975 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12975 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12975 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12975 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12975 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12975 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12975 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12975 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12975 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12975 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12975 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12975 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12975 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12975 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12975 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051919143187 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12975) ≤ 0.010484242328 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12975 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035424387669)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010484242328 + 2 * 0.737676 / 12975) := by gcongr
    _ ≤ (0.051919143187 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12975 12 ≤ 0.0015 := by
  exact BstLean.Part269.S25.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12975

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12975
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560515741025 : ℝ) ≤ plow 12975 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12975) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052472021006)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001350112376) : eMP 12975 0.011 xi bn ≤ 0.001162687966 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12975 : ℝ) * (1 - 0.011))) ≤ 0.000574920892 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001350112376 / (12975 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000574920892 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000574920892 : ℝ) + 3.141593 * 0.052472021006 / (12975 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001162687966 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052472021006)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001350112376) : PiBarMP 12975 12 0.011 xi bn ≤ 0.159515963720 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12975 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036743875354 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.279631884995 : ℝ) ≤ √((12975 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.907857498945 : ℝ) ≤ √(12975 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12975) ≤ 0.122312969173 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036743875354 + 0.052472021006 * 1.772454 / (2 * (113.279631884995 : ℝ))) * (1 + 0.001162687966) +
        8 / (12975 * 113.907857498945) + 0.122312969173 := by gcongr
    _ ≤ (0.159515963720 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052472021006)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001350112376) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280986864628) :
    parallelOracle 12975 0.011 xi bn cd ≤ 0.160485274912 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12975 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12975 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560515741025 : ℝ) ≤ plow 12975 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.907857498945 : ℝ) ≤ √(12975 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280986864628 : ℝ) / (2 * 0.560515741025 * 113.907857498945)) * 0.159515963720 +
        0.280986864628 ^ 2 / (2 * 0.560515741025 * 113.907857498945) := by gcongr
    _ ≤ (0.160485274912 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052472021006) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001350112376)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280986864628) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12975 12975 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560515741025 : ℝ) ≤ plow 12975 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.907857498945 : ℝ) ≤ √(12975 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12975 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12975 Θ 1.22 ≤ 0.011641870273 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.907857498945 := by gcongr <;> linarith
      _ ≤ (0.011641870273 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12975 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12975 12975 0.011 ≤ 0.008391756041 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12975 12975 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12975 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12975 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12975 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12975 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160485274912 + 0.011641870273 + (0.008391756041 : ℝ) *
        (1 + 2 * (0.280986864628 + 0.011641870273) / (0.560515741025 * 113.907857498945))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12975]

end BstLean.Part269.N12975

/-! The original eight local profiles supply actual 12975 moment certificates. -/
namespace BstLean.Part269.N12975
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12975 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12975 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12975 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052472021006 ∧
    0 ≤ bN 12975 BstLean.Part154.csC (groupTheta g) ∧ bN 12975 BstLean.Part154.csC (groupTheta g) ≤ 0.001350112376 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12975 12975 0.011
      (momentAllowance 12975 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12975 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12975 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12975 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12975 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12975 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229067721441 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12975 0.011
      (momentAllowance 12975 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12975 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12975
/-! The actual computed-centre upper energy formula at 12975. -/
namespace BstLean.Part269.N12975
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12975

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12975
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12975)
open BstLean.Part268 (cell12975)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084725834533
  | 2 => 0.085655380917
  | 3 => 0.086581269994
  | 4 => 0.087504497341
  | 5 => 0.088426279641
  | 6 => 0.089348089083
  | 7 => 0.090271691291
  | 8 => 0.091199186875
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12975 12975 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12975 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003274156000 + 0.003221457154 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S25.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12975

/-! Actual upper energy certificates on all 43 source endpoints at 12975. -/
namespace BstLean.Part269.N12975
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12975)
open BstLean.Part268 (cell12975)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12975 (gMinus 12975) (1 - (cell12975 i).lower) ≤ 1 ∧
    energyUpper 12975 (gMinus 12975) (BstLean.Part211.gPlus 12975)
      (finiteEnergy 12975 12975 0.011) (1 - (cell12975 i).lower) ≤
      (cell12975 i).energy := by
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
      have E := BstLean.Part269.S25.uniformEnergy10 (n := 12975) (by norm_num)
        (q := 1 - (cell12975 ⟨10,by decide⟩).lower)
        (by norm_num [cell12975]) (by norm_num [cell12975])
      exact ⟨E.1,E.2.trans (by norm_num [cell12975])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy11 (n := 12975) (by norm_num)
        (q := 1 - (cell12975 ⟨11,by decide⟩).lower)
        (by norm_num [cell12975]) (by norm_num [cell12975])
      exact ⟨E.1,E.2.trans (by norm_num [cell12975])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy12 (n := 12975) (by norm_num)
        (q := 1 - (cell12975 ⟨12,by decide⟩).lower)
        (by norm_num [cell12975]) (by norm_num [cell12975])
      exact ⟨E.1,E.2.trans (by norm_num [cell12975])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy13 (n := 12975) (by norm_num)
        (q := 1 - (cell12975 ⟨13,by decide⟩).lower)
        (by norm_num [cell12975]) (by norm_num [cell12975])
      exact ⟨E.1,E.2.trans (by norm_num [cell12975])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy14 (n := 12975) (by norm_num)
        (q := 1 - (cell12975 ⟨14,by decide⟩).lower)
        (by norm_num [cell12975]) (by norm_num [cell12975])
      exact ⟨E.1,E.2.trans (by norm_num [cell12975])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy15 (n := 12975) (by norm_num)
        (q := 1 - (cell12975 ⟨15,by decide⟩).lower)
        (by norm_num [cell12975]) (by norm_num [cell12975])
      exact ⟨E.1,E.2.trans (by norm_num [cell12975])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy16 (n := 12975) (by norm_num)
        (q := 1 - (cell12975 ⟨16,by decide⟩).lower)
        (by norm_num [cell12975]) (by norm_num [cell12975])
      exact ⟨E.1,E.2.trans (by norm_num [cell12975])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy17 (n := 12975) (by norm_num)
        (q := 1 - (cell12975 ⟨17,by decide⟩).lower)
        (by norm_num [cell12975]) (by norm_num [cell12975])
      exact ⟨E.1,E.2.trans (by norm_num [cell12975])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy18 (n := 12975) (by norm_num)
        (q := 1 - (cell12975 ⟨18,by decide⟩).lower)
        (by norm_num [cell12975]) (by norm_num [cell12975])
      exact ⟨E.1,E.2.trans (by norm_num [cell12975])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy19 (n := 12975) (by norm_num)
        (q := 1 - (cell12975 ⟨19,by decide⟩).lower)
        (by norm_num [cell12975]) (by norm_num [cell12975])
      exact ⟨E.1,E.2.trans (by norm_num [cell12975])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy20 (n := 12975) (by norm_num)
        (q := 1 - (cell12975 ⟨20,by decide⟩).lower)
        (by norm_num [cell12975]) (by norm_num [cell12975])
      exact ⟨E.1,E.2.trans (by norm_num [cell12975])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy21 (n := 12975) (by norm_num)
        (q := 1 - (cell12975 ⟨21,by decide⟩).lower)
        (by norm_num [cell12975]) (by norm_num [cell12975])
      exact ⟨E.1,E.2.trans (by norm_num [cell12975])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy22 (n := 12975) (by norm_num)
        (q := 1 - (cell12975 ⟨22,by decide⟩).lower)
        (by norm_num [cell12975]) (by norm_num [cell12975])
      exact ⟨E.1,E.2.trans (by norm_num [cell12975])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy23 (n := 12975) (by norm_num)
        (q := 1 - (cell12975 ⟨23,by decide⟩).lower)
        (by norm_num [cell12975]) (by norm_num [cell12975])
      exact ⟨E.1,E.2.trans (by norm_num [cell12975])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy24 (n := 12975) (by norm_num)
        (q := 1 - (cell12975 ⟨24,by decide⟩).lower)
        (by norm_num [cell12975]) (by norm_num [cell12975])
      exact ⟨E.1,E.2.trans (by norm_num [cell12975])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy25 (n := 12975) (by norm_num)
        (q := 1 - (cell12975 ⟨25,by decide⟩).lower)
        (by norm_num [cell12975]) (by norm_num [cell12975])
      exact ⟨E.1,E.2.trans (by norm_num [cell12975])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy26 (n := 12975) (by norm_num)
        (q := 1 - (cell12975 ⟨26,by decide⟩).lower)
        (by norm_num [cell12975]) (by norm_num [cell12975])
      exact ⟨E.1,E.2.trans (by norm_num [cell12975])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy27 (n := 12975) (by norm_num)
        (q := 1 - (cell12975 ⟨27,by decide⟩).lower)
        (by norm_num [cell12975]) (by norm_num [cell12975])
      exact ⟨E.1,E.2.trans (by norm_num [cell12975])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy28 (n := 12975) (by norm_num)
        (q := 1 - (cell12975 ⟨28,by decide⟩).lower)
        (by norm_num [cell12975]) (by norm_num [cell12975])
      exact ⟨E.1,E.2.trans (by norm_num [cell12975])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy29 (n := 12975) (by norm_num)
        (q := 1 - (cell12975 ⟨29,by decide⟩).lower)
        (by norm_num [cell12975]) (by norm_num [cell12975])
      exact ⟨E.1,E.2.trans (by norm_num [cell12975])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy30 (n := 12975) (by norm_num)
        (q := 1 - (cell12975 ⟨30,by decide⟩).lower)
        (by norm_num [cell12975]) (by norm_num [cell12975])
      exact ⟨E.1,E.2.trans (by norm_num [cell12975])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy31 (n := 12975) (by norm_num)
        (q := 1 - (cell12975 ⟨31,by decide⟩).lower)
        (by norm_num [cell12975]) (by norm_num [cell12975])
      exact ⟨E.1,E.2.trans (by norm_num [cell12975])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy32 (n := 12975) (by norm_num)
        (q := 1 - (cell12975 ⟨32,by decide⟩).lower)
        (by norm_num [cell12975]) (by norm_num [cell12975])
      exact ⟨E.1,E.2.trans (by norm_num [cell12975])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy33 (n := 12975) (by norm_num)
        (q := 1 - (cell12975 ⟨33,by decide⟩).lower)
        (by norm_num [cell12975]) (by norm_num [cell12975])
      exact ⟨E.1,E.2.trans (by norm_num [cell12975])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy34 (n := 12975) (by norm_num)
        (q := 1 - (cell12975 ⟨34,by decide⟩).lower)
        (by norm_num [cell12975]) (by norm_num [cell12975])
      exact ⟨E.1,E.2.trans (by norm_num [cell12975])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy35 (n := 12975) (by norm_num)
        (q := 1 - (cell12975 ⟨35,by decide⟩).lower)
        (by norm_num [cell12975]) (by norm_num [cell12975])
      exact ⟨E.1,E.2.trans (by norm_num [cell12975])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy36 (n := 12975) (by norm_num)
        (q := 1 - (cell12975 ⟨36,by decide⟩).lower)
        (by norm_num [cell12975]) (by norm_num [cell12975])
      exact ⟨E.1,E.2.trans (by norm_num [cell12975])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy37 (n := 12975) (by norm_num)
        (q := 1 - (cell12975 ⟨37,by decide⟩).lower)
        (by norm_num [cell12975]) (by norm_num [cell12975])
      exact ⟨E.1,E.2.trans (by norm_num [cell12975])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy38 (n := 12975) (by norm_num)
        (q := 1 - (cell12975 ⟨38,by decide⟩).lower)
        (by norm_num [cell12975]) (by norm_num [cell12975])
      exact ⟨E.1,E.2.trans (by norm_num [cell12975])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy39 (n := 12975) (by norm_num)
        (q := 1 - (cell12975 ⟨39,by decide⟩).lower)
        (by norm_num [cell12975]) (by norm_num [cell12975])
      exact ⟨E.1,E.2.trans (by norm_num [cell12975])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy40 (n := 12975) (by norm_num)
        (q := 1 - (cell12975 ⟨40,by decide⟩).lower)
        (by norm_num [cell12975]) (by norm_num [cell12975])
      exact ⟨E.1,E.2.trans (by norm_num [cell12975])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy41 (n := 12975) (by norm_num)
        (q := 1 - (cell12975 ⟨41,by decide⟩).lower)
        (by norm_num [cell12975]) (by norm_num [cell12975])
      exact ⟨E.1,E.2.trans (by norm_num [cell12975])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy42 (n := 12975) (by norm_num)
        (q := 1 - (cell12975 ⟨42,by decide⟩).lower)
        (by norm_num [cell12975]) (by norm_num [cell12975])
      exact ⟨E.1,E.2.trans (by norm_num [cell12975])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy43 (n := 12975) (by norm_num)
        (q := 1 - (cell12975 ⟨43,by decide⟩).lower)
        (by norm_num [cell12975]) (by norm_num [cell12975])
      exact ⟨E.1,E.2.trans (by norm_num [cell12975])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy44 (n := 12975) (by norm_num)
        (q := 1 - (cell12975 ⟨44,by decide⟩).lower)
        (by norm_num [cell12975]) (by norm_num [cell12975])
      exact ⟨E.1,E.2.trans (by norm_num [cell12975])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy45 (n := 12975) (by norm_num)
        (q := 1 - (cell12975 ⟨45,by decide⟩).lower)
        (by norm_num [cell12975]) (by norm_num [cell12975])
      exact ⟨E.1,E.2.trans (by norm_num [cell12975])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy46 (n := 12975) (by norm_num)
        (q := 1 - (cell12975 ⟨46,by decide⟩).lower)
        (by norm_num [cell12975]) (by norm_num [cell12975])
      exact ⟨E.1,E.2.trans (by norm_num [cell12975])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy47 (n := 12975) (by norm_num)
        (q := 1 - (cell12975 ⟨47,by decide⟩).lower)
        (by norm_num [cell12975]) (by norm_num [cell12975])
      exact ⟨E.1,E.2.trans (by norm_num [cell12975])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy48 (n := 12975) (by norm_num)
        (q := 1 - (cell12975 ⟨48,by decide⟩).lower)
        (by norm_num [cell12975]) (by norm_num [cell12975])
      exact ⟨E.1,E.2.trans (by norm_num [cell12975])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy49 (n := 12975) (by norm_num)
        (q := 1 - (cell12975 ⟨49,by decide⟩).lower)
        (by norm_num [cell12975]) (by norm_num [cell12975])
      exact ⟨E.1,E.2.trans (by norm_num [cell12975])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy50 (n := 12975) (by norm_num)
        (q := 1 - (cell12975 ⟨50,by decide⟩).lower)
        (by norm_num [cell12975]) (by norm_num [cell12975])
      exact ⟨E.1,E.2.trans (by norm_num [cell12975])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy51 (n := 12975) (by norm_num)
        (q := 1 - (cell12975 ⟨51,by decide⟩).lower)
        (by norm_num [cell12975]) (by norm_num [cell12975])
      exact ⟨E.1,E.2.trans (by norm_num [cell12975])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy52 (n := 12975) (by norm_num)
        (q := 1 - (cell12975 ⟨52,by decide⟩).lower)
        (by norm_num [cell12975]) (by norm_num [cell12975])
      exact ⟨E.1,E.2.trans (by norm_num [cell12975])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12975

/-! Source-cell containment and simple scalar guards at 12975. -/
namespace BstLean.Part269.N12975
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12975)
open BstLean.Part268 (cell12975)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12975 ⟨10,by decide⟩).lower ∧ (cell12975 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12975 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12975 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12975 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12975 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12975 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12975,cell12975,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12975 ⟨11,by decide⟩).lower ∧ (cell12975 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12975 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12975 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12975 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12975 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12975 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12975,cell12975,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12975 ⟨12,by decide⟩).lower ∧ (cell12975 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12975 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12975 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12975 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12975 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12975 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12975,cell12975,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12975 ⟨13,by decide⟩).lower ∧ (cell12975 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12975 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12975 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12975 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12975 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12975 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12975,cell12975,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12975 ⟨14,by decide⟩).lower ∧ (cell12975 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12975 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12975 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12975 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12975 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12975 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12975,cell12975,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12975 ⟨15,by decide⟩).lower ∧ (cell12975 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12975 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12975 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12975 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12975 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12975 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12975,cell12975,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12975 ⟨16,by decide⟩).lower ∧ (cell12975 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12975 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12975 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12975 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12975 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12975 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12975,cell12975,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12975 ⟨17,by decide⟩).lower ∧ (cell12975 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12975 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12975 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12975 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12975 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12975 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12975,cell12975,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12975 ⟨18,by decide⟩).lower ∧ (cell12975 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12975 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12975 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12975 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12975 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12975 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12975,cell12975,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12975 ⟨19,by decide⟩).lower ∧ (cell12975 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12975 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12975 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12975 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12975 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12975 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12975,cell12975,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12975 ⟨20,by decide⟩).lower ∧ (cell12975 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12975 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12975 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12975 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12975 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12975 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12975,cell12975,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12975 ⟨21,by decide⟩).lower ∧ (cell12975 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12975 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12975 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12975 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12975 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12975 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12975,cell12975,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12975 ⟨22,by decide⟩).lower ∧ (cell12975 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12975 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12975 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12975 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12975 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12975 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12975,cell12975,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12975 ⟨23,by decide⟩).lower ∧ (cell12975 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12975 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12975 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12975 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12975 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12975 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12975,cell12975,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12975 ⟨24,by decide⟩).lower ∧ (cell12975 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12975 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12975 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12975 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12975 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12975 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12975,cell12975,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12975 ⟨25,by decide⟩).lower ∧ (cell12975 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12975 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12975 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12975 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12975 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12975 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12975,cell12975,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12975 ⟨26,by decide⟩).lower ∧ (cell12975 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12975 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12975 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12975 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12975 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12975 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12975,cell12975,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12975 ⟨27,by decide⟩).lower ∧ (cell12975 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12975 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12975 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12975 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12975 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12975 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12975,cell12975,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12975 ⟨28,by decide⟩).lower ∧ (cell12975 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12975 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12975 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12975 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12975 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12975 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12975,cell12975,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12975 ⟨29,by decide⟩).lower ∧ (cell12975 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12975 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12975 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12975 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12975 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12975 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12975,cell12975,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12975 ⟨30,by decide⟩).lower ∧ (cell12975 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12975 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12975 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12975 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12975 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12975 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12975,cell12975,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12975 ⟨31,by decide⟩).lower ∧ (cell12975 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12975 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12975 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12975 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12975 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12975 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12975,cell12975,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12975 ⟨32,by decide⟩).lower ∧ (cell12975 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12975 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12975 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12975 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12975 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12975 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12975,cell12975,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12975 ⟨33,by decide⟩).lower ∧ (cell12975 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12975 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12975 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12975 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12975 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12975 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12975,cell12975,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12975 ⟨34,by decide⟩).lower ∧ (cell12975 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12975 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12975 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12975 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12975 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12975 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12975,cell12975,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12975 ⟨35,by decide⟩).lower ∧ (cell12975 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12975 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12975 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12975 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12975 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12975 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12975,cell12975,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12975 ⟨36,by decide⟩).lower ∧ (cell12975 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12975 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12975 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12975 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12975 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12975 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12975,cell12975,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12975 ⟨37,by decide⟩).lower ∧ (cell12975 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12975 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12975 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12975 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12975 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12975 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12975,cell12975,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12975 ⟨38,by decide⟩).lower ∧ (cell12975 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12975 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12975 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12975 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12975 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12975 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12975,cell12975,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12975 ⟨39,by decide⟩).lower ∧ (cell12975 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12975 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12975 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12975 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12975 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12975 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12975,cell12975,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12975 ⟨40,by decide⟩).lower ∧ (cell12975 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12975 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12975 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12975 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12975 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12975 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12975,cell12975,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12975 ⟨41,by decide⟩).lower ∧ (cell12975 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12975 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12975 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12975 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12975 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12975 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12975,cell12975,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12975 ⟨42,by decide⟩).lower ∧ (cell12975 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12975 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12975 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12975 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12975 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12975 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12975,cell12975,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12975 ⟨43,by decide⟩).lower ∧ (cell12975 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12975 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12975 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12975 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12975 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12975 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12975,cell12975,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12975 ⟨44,by decide⟩).lower ∧ (cell12975 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12975 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12975 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12975 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12975 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12975 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12975,cell12975,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12975 ⟨45,by decide⟩).lower ∧ (cell12975 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12975 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12975 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12975 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12975 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12975 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12975,cell12975,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12975 ⟨46,by decide⟩).lower ∧ (cell12975 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12975 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12975 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12975 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12975 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12975 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12975,cell12975,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12975 ⟨47,by decide⟩).lower ∧ (cell12975 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12975 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12975 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12975 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12975 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12975 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12975,cell12975,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12975 ⟨48,by decide⟩).lower ∧ (cell12975 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12975 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12975 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12975 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12975 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12975 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12975,cell12975,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12975 ⟨49,by decide⟩).lower ∧ (cell12975 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12975 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12975 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12975 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12975 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12975 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12975,cell12975,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12975 ⟨50,by decide⟩).lower ∧ (cell12975 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12975 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12975 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12975 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12975 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12975 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12975,cell12975,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12975 ⟨51,by decide⟩).lower ∧ (cell12975 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12975 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12975 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12975 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12975 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12975 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12975,cell12975,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12975 ⟨52,by decide⟩).lower ∧ (cell12975 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12975 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12975 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12975 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12975 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12975 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12975,cell12975,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12975 i).lower ∧
    (cell12975 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12975 i).upper ≤ (0.532 : ℝ) ∧
    (cell12975 i).centre ≤ (0.1 : ℝ) ∧ (cell12975 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12975 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12975 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12975

/-! The local source numeric instances at 12975 have no network premises. -/
namespace BstLean.Part269.N12975
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12975)
open BstLean.Part268 (cell12975)

noncomputable def sourceNumerics12975 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12975 (cell12975 i)
      scalarRow12975.M scalarRow12975.H scalarRow12975.xi := by
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
    energy_allowance := scalarRow12975.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12975]
    centre_nonneg := (scalarRow12975.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D25.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12975])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12975
/-! Actual 12976 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12976
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12976 ≤ (1.035423010767 : ℝ) := by
  have hr : (113.912246927185 : ℝ) ≤ √(12976 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.912246927185 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12976 12976 (11 / 1000) ≤
    (0.008391432675 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12976) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.912246927185 : ℝ) ≤ √(12976 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12976)
  have hdiv : K / √(12976 : ℝ) ≤ K / 113.912246927185 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.912246927185 ≤ (0.008391432675 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12976.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12976 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12976 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12976 := gPlus_lower 12976
end BstLean.Part269.N12976

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12976
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035423010766 : ℝ) ≤ wn 12976 := by
  have hn : √(12976 : ℝ) ≤ 113.912246927186 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12976 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.912246927186 ≤ 2 / √(12976 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000246431435 : ℝ) ≤ rhoBar 12976 BstLean.Part154.csC ∧
    rhoBar 12976 BstLean.Part154.csC ≤ 0.000246431817 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035423010766 : ℝ) / (1.295212 * 12976) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035423010767 : ℝ) / (1.29521 * 12976) := by gcongr
      _ ≤ (0.000246431817 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12976 BstLean.Part154.csC) ≤ 0.000985787997 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12976 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12976 BstLean.Part154.csC) (piBar (rhoBar 12976 BstLean.Part154.csC)) ≤ 0.000188226095 ∧
    cc1 (rhoBar 12976 BstLean.Part154.csC) (piBar (rhoBar 12976 BstLean.Part154.csC)) ≤ 0.000119769553 ∧
    cc2 (rhoBar 12976 BstLean.Part154.csC) ≤ 0.000069527190 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12976 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12976 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12976 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12976 BstLean.Part154.csC * nuR (rhoBar 12976 BstLean.Part154.csC)) ≤ 0.000492878817 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000246431817 : ℝ) * 0.000985787997 := by gcongr
      _ ≤ (0.000492878817 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12976 BstLean.Part154.csC) * nuR (rhoBar 12976 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000985787997 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12976 BstLean.Part154.csC) * rhoBar 12976 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000246431817 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000246431817 / 2 + 0.399 * 0.000985787997 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000188226095 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000492878817 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119769553 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000246431817 / 1.414213562 := by gcongr
      _ ≤ (0.000069527190 : ℝ) := by norm_num

end BstLean.Part269.N12976

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12976
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12976 BstLean.Part154.csC) (piBar (rhoBar 12976 BstLean.Part154.csC)) ≤ 1.53001E-7 := by
  have hr0 : 0 ≤ rhoBar 12976 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12976 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12976 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12976 BstLean.Part154.csC) (piBar (rhoBar 12976 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12976 BstLean.Part154.csC) (piBar (rhoBar 12976 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12976 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000188226095 : ℝ) ^ 2 + 0.000119769553 ^ 2 + 3 * 0.000069527190 ^ 2 +
        2 * 0.797885 * 0.000188226095 * 0.000119769553 + 2 * 0.000188226095 * 0.000069527190 +
        4 * 0.797885 * 0.000119769553 * 0.000069527190 := by gcongr
    _ ≤ (1.53001E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12976 BstLean.Part154.csC Θ ≤ 0.002571437465 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12976 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12976 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12976 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12976 BstLean.Part154.csC) (piBar (rhoBar 12976 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12976 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035423010767 * 1.53001E-7 / (0.000246431435 : ℝ) := by gcongr
    _ ≤ 0.002571437465 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12976 BstLean.Part154.csC Θ ≤ 0.002852089582 + 0.000649762729 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12976 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12976 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12976 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035423010767 : ℝ) * ((2 * Θ * 0.000246431817 +
        (6863 / 10000) * 0.000246431817 * 12976 * 0.000985787997) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002852089582 + 0.000649762729 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12976 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12976 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12976 0.011 Θ ∧ gammaRatio 12976 0.011 Θ ≤ 0.000084716886 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12976 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035423010767 : ℝ) * 0.525 / ((1 - 0.011) * 12976) := by gcongr
      _ ≤ (0.000084716886 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12976 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12976 0.011 Θ) :=
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
    badAllowance 12976 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000421835223 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12976 BstLean.Part154.csC) 1.22 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 2 (rhoBar 12976 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12976 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12976 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12976 0.011 Θ) 1.12 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 1 (gammaRatio 12976 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12976 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12976 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12976 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12976 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035423010767 : ℝ) * 12976 *
        (1.5230E-8 / 1.1045361 + 1.8602E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000421835223 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12976 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003273924805 + 0.003221200194 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12976

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12976
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12976 BstLean.Part154.csC) (piBar (rhoBar 12976 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12976 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12976 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12976 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12976 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12976 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12976 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12976 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12976 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12976 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12976 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12976 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12976 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12976 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12976 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051917121104 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12976) ≤ 0.010483838335 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12976 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035423010767)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010483838335 + 2 * 0.737676 / 12976) := by gcongr
    _ ≤ (0.051917121104 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12976 12 ≤ 0.0015 := by
  exact BstLean.Part269.S25.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12976

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12976
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560515784348 : ℝ) ≤ plow 12976 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12976) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052471654907)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001350004670) : eMP 12976 0.011 xi bn ≤ 0.001162596714 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12976 : ℝ) * (1 - 0.011))) ≤ 0.000574875806 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001350004670 / (12976 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000574875806 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000574875806 : ℝ) + 3.141593 * 0.052471654907 / (12976 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001162596714 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052471654907)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001350004670) : PiBarMP 12976 12 0.011 xi bn ≤ 0.159509760498 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12976 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036742409693 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.283997104621 : ℝ) ≤ √((12976 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.912246927185 : ℝ) ≤ √(12976 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12976) ≤ 0.122308256036 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036742409693 + 0.052471654907 * 1.772454 / (2 * (113.283997104621 : ℝ))) * (1 + 0.001162596714) +
        8 / (12976 * 113.912246927185) + 0.122308256036 := by gcongr
    _ ≤ (0.159509760498 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052471654907)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001350004670) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280984043437) :
    parallelOracle 12976 0.011 xi bn cd ≤ 0.160479004676 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12976 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12976 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560515784348 : ℝ) ≤ plow 12976 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.912246927185 : ℝ) ≤ √(12976 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280984043437 : ℝ) / (2 * 0.560515784348 * 113.912246927185)) * 0.159509760498 +
        0.280984043437 ^ 2 / (2 * 0.560515784348 * 113.912246927185) := by gcongr
    _ ≤ (0.160479004676 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052471654907) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001350004670)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280984043437) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12976 12976 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560515784348 : ℝ) ≤ plow 12976 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.912246927185 : ℝ) ≤ √(12976 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12976 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12976 Θ 1.22 ≤ 0.011641421672 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.912246927185 := by gcongr <;> linarith
      _ ≤ (0.011641421672 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12976 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12976 12976 0.011 ≤ 0.008391432675 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12976 12976 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12976 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12976 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12976 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12976 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160479004676 + 0.011641421672 + (0.008391432675 : ℝ) *
        (1 + 2 * (0.280984043437 + 0.011641421672) / (0.560515784348 * 113.912246927185))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12976]

end BstLean.Part269.N12976

/-! The original eight local profiles supply actual 12976 moment certificates. -/
namespace BstLean.Part269.N12976
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12976 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12976 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12976 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052471654907 ∧
    0 ≤ bN 12976 BstLean.Part154.csC (groupTheta g) ∧ bN 12976 BstLean.Part154.csC (groupTheta g) ≤ 0.001350004670 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12976 12976 0.011
      (momentAllowance 12976 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12976 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12976 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12976 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12976 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12976 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229066922333 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12976 0.011
      (momentAllowance 12976 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12976 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12976
/-! The actual computed-centre upper energy formula at 12976. -/
namespace BstLean.Part269.N12976
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12976

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12976
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12976)
open BstLean.Part268 (cell12976)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084723195907
  | 2 => 0.085652707019
  | 3 => 0.086578555393
  | 4 => 0.087501735339
  | 5 => 0.088423462045
  | 6 => 0.089345205943
  | 7 => 0.090268730607
  | 8 => 0.091196134271
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12976 12976 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12976 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003274156000 + 0.003221457154 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S25.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12976

/-! Actual upper energy certificates on all 43 source endpoints at 12976. -/
namespace BstLean.Part269.N12976
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12976)
open BstLean.Part268 (cell12976)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12976 (gMinus 12976) (1 - (cell12976 i).lower) ≤ 1 ∧
    energyUpper 12976 (gMinus 12976) (BstLean.Part211.gPlus 12976)
      (finiteEnergy 12976 12976 0.011) (1 - (cell12976 i).lower) ≤
      (cell12976 i).energy := by
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
      have E := BstLean.Part269.S25.uniformEnergy10 (n := 12976) (by norm_num)
        (q := 1 - (cell12976 ⟨10,by decide⟩).lower)
        (by norm_num [cell12976]) (by norm_num [cell12976])
      exact ⟨E.1,E.2.trans (by norm_num [cell12976])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy11 (n := 12976) (by norm_num)
        (q := 1 - (cell12976 ⟨11,by decide⟩).lower)
        (by norm_num [cell12976]) (by norm_num [cell12976])
      exact ⟨E.1,E.2.trans (by norm_num [cell12976])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy12 (n := 12976) (by norm_num)
        (q := 1 - (cell12976 ⟨12,by decide⟩).lower)
        (by norm_num [cell12976]) (by norm_num [cell12976])
      exact ⟨E.1,E.2.trans (by norm_num [cell12976])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy13 (n := 12976) (by norm_num)
        (q := 1 - (cell12976 ⟨13,by decide⟩).lower)
        (by norm_num [cell12976]) (by norm_num [cell12976])
      exact ⟨E.1,E.2.trans (by norm_num [cell12976])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy14 (n := 12976) (by norm_num)
        (q := 1 - (cell12976 ⟨14,by decide⟩).lower)
        (by norm_num [cell12976]) (by norm_num [cell12976])
      exact ⟨E.1,E.2.trans (by norm_num [cell12976])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy15 (n := 12976) (by norm_num)
        (q := 1 - (cell12976 ⟨15,by decide⟩).lower)
        (by norm_num [cell12976]) (by norm_num [cell12976])
      exact ⟨E.1,E.2.trans (by norm_num [cell12976])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy16 (n := 12976) (by norm_num)
        (q := 1 - (cell12976 ⟨16,by decide⟩).lower)
        (by norm_num [cell12976]) (by norm_num [cell12976])
      exact ⟨E.1,E.2.trans (by norm_num [cell12976])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy17 (n := 12976) (by norm_num)
        (q := 1 - (cell12976 ⟨17,by decide⟩).lower)
        (by norm_num [cell12976]) (by norm_num [cell12976])
      exact ⟨E.1,E.2.trans (by norm_num [cell12976])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy18 (n := 12976) (by norm_num)
        (q := 1 - (cell12976 ⟨18,by decide⟩).lower)
        (by norm_num [cell12976]) (by norm_num [cell12976])
      exact ⟨E.1,E.2.trans (by norm_num [cell12976])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy19 (n := 12976) (by norm_num)
        (q := 1 - (cell12976 ⟨19,by decide⟩).lower)
        (by norm_num [cell12976]) (by norm_num [cell12976])
      exact ⟨E.1,E.2.trans (by norm_num [cell12976])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy20 (n := 12976) (by norm_num)
        (q := 1 - (cell12976 ⟨20,by decide⟩).lower)
        (by norm_num [cell12976]) (by norm_num [cell12976])
      exact ⟨E.1,E.2.trans (by norm_num [cell12976])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy21 (n := 12976) (by norm_num)
        (q := 1 - (cell12976 ⟨21,by decide⟩).lower)
        (by norm_num [cell12976]) (by norm_num [cell12976])
      exact ⟨E.1,E.2.trans (by norm_num [cell12976])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy22 (n := 12976) (by norm_num)
        (q := 1 - (cell12976 ⟨22,by decide⟩).lower)
        (by norm_num [cell12976]) (by norm_num [cell12976])
      exact ⟨E.1,E.2.trans (by norm_num [cell12976])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy23 (n := 12976) (by norm_num)
        (q := 1 - (cell12976 ⟨23,by decide⟩).lower)
        (by norm_num [cell12976]) (by norm_num [cell12976])
      exact ⟨E.1,E.2.trans (by norm_num [cell12976])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy24 (n := 12976) (by norm_num)
        (q := 1 - (cell12976 ⟨24,by decide⟩).lower)
        (by norm_num [cell12976]) (by norm_num [cell12976])
      exact ⟨E.1,E.2.trans (by norm_num [cell12976])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy25 (n := 12976) (by norm_num)
        (q := 1 - (cell12976 ⟨25,by decide⟩).lower)
        (by norm_num [cell12976]) (by norm_num [cell12976])
      exact ⟨E.1,E.2.trans (by norm_num [cell12976])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy26 (n := 12976) (by norm_num)
        (q := 1 - (cell12976 ⟨26,by decide⟩).lower)
        (by norm_num [cell12976]) (by norm_num [cell12976])
      exact ⟨E.1,E.2.trans (by norm_num [cell12976])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy27 (n := 12976) (by norm_num)
        (q := 1 - (cell12976 ⟨27,by decide⟩).lower)
        (by norm_num [cell12976]) (by norm_num [cell12976])
      exact ⟨E.1,E.2.trans (by norm_num [cell12976])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy28 (n := 12976) (by norm_num)
        (q := 1 - (cell12976 ⟨28,by decide⟩).lower)
        (by norm_num [cell12976]) (by norm_num [cell12976])
      exact ⟨E.1,E.2.trans (by norm_num [cell12976])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy29 (n := 12976) (by norm_num)
        (q := 1 - (cell12976 ⟨29,by decide⟩).lower)
        (by norm_num [cell12976]) (by norm_num [cell12976])
      exact ⟨E.1,E.2.trans (by norm_num [cell12976])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy30 (n := 12976) (by norm_num)
        (q := 1 - (cell12976 ⟨30,by decide⟩).lower)
        (by norm_num [cell12976]) (by norm_num [cell12976])
      exact ⟨E.1,E.2.trans (by norm_num [cell12976])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy31 (n := 12976) (by norm_num)
        (q := 1 - (cell12976 ⟨31,by decide⟩).lower)
        (by norm_num [cell12976]) (by norm_num [cell12976])
      exact ⟨E.1,E.2.trans (by norm_num [cell12976])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy32 (n := 12976) (by norm_num)
        (q := 1 - (cell12976 ⟨32,by decide⟩).lower)
        (by norm_num [cell12976]) (by norm_num [cell12976])
      exact ⟨E.1,E.2.trans (by norm_num [cell12976])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy33 (n := 12976) (by norm_num)
        (q := 1 - (cell12976 ⟨33,by decide⟩).lower)
        (by norm_num [cell12976]) (by norm_num [cell12976])
      exact ⟨E.1,E.2.trans (by norm_num [cell12976])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy34 (n := 12976) (by norm_num)
        (q := 1 - (cell12976 ⟨34,by decide⟩).lower)
        (by norm_num [cell12976]) (by norm_num [cell12976])
      exact ⟨E.1,E.2.trans (by norm_num [cell12976])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy35 (n := 12976) (by norm_num)
        (q := 1 - (cell12976 ⟨35,by decide⟩).lower)
        (by norm_num [cell12976]) (by norm_num [cell12976])
      exact ⟨E.1,E.2.trans (by norm_num [cell12976])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy36 (n := 12976) (by norm_num)
        (q := 1 - (cell12976 ⟨36,by decide⟩).lower)
        (by norm_num [cell12976]) (by norm_num [cell12976])
      exact ⟨E.1,E.2.trans (by norm_num [cell12976])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy37 (n := 12976) (by norm_num)
        (q := 1 - (cell12976 ⟨37,by decide⟩).lower)
        (by norm_num [cell12976]) (by norm_num [cell12976])
      exact ⟨E.1,E.2.trans (by norm_num [cell12976])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy38 (n := 12976) (by norm_num)
        (q := 1 - (cell12976 ⟨38,by decide⟩).lower)
        (by norm_num [cell12976]) (by norm_num [cell12976])
      exact ⟨E.1,E.2.trans (by norm_num [cell12976])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy39 (n := 12976) (by norm_num)
        (q := 1 - (cell12976 ⟨39,by decide⟩).lower)
        (by norm_num [cell12976]) (by norm_num [cell12976])
      exact ⟨E.1,E.2.trans (by norm_num [cell12976])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy40 (n := 12976) (by norm_num)
        (q := 1 - (cell12976 ⟨40,by decide⟩).lower)
        (by norm_num [cell12976]) (by norm_num [cell12976])
      exact ⟨E.1,E.2.trans (by norm_num [cell12976])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy41 (n := 12976) (by norm_num)
        (q := 1 - (cell12976 ⟨41,by decide⟩).lower)
        (by norm_num [cell12976]) (by norm_num [cell12976])
      exact ⟨E.1,E.2.trans (by norm_num [cell12976])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy42 (n := 12976) (by norm_num)
        (q := 1 - (cell12976 ⟨42,by decide⟩).lower)
        (by norm_num [cell12976]) (by norm_num [cell12976])
      exact ⟨E.1,E.2.trans (by norm_num [cell12976])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy43 (n := 12976) (by norm_num)
        (q := 1 - (cell12976 ⟨43,by decide⟩).lower)
        (by norm_num [cell12976]) (by norm_num [cell12976])
      exact ⟨E.1,E.2.trans (by norm_num [cell12976])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy44 (n := 12976) (by norm_num)
        (q := 1 - (cell12976 ⟨44,by decide⟩).lower)
        (by norm_num [cell12976]) (by norm_num [cell12976])
      exact ⟨E.1,E.2.trans (by norm_num [cell12976])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy45 (n := 12976) (by norm_num)
        (q := 1 - (cell12976 ⟨45,by decide⟩).lower)
        (by norm_num [cell12976]) (by norm_num [cell12976])
      exact ⟨E.1,E.2.trans (by norm_num [cell12976])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy46 (n := 12976) (by norm_num)
        (q := 1 - (cell12976 ⟨46,by decide⟩).lower)
        (by norm_num [cell12976]) (by norm_num [cell12976])
      exact ⟨E.1,E.2.trans (by norm_num [cell12976])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy47 (n := 12976) (by norm_num)
        (q := 1 - (cell12976 ⟨47,by decide⟩).lower)
        (by norm_num [cell12976]) (by norm_num [cell12976])
      exact ⟨E.1,E.2.trans (by norm_num [cell12976])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy48 (n := 12976) (by norm_num)
        (q := 1 - (cell12976 ⟨48,by decide⟩).lower)
        (by norm_num [cell12976]) (by norm_num [cell12976])
      exact ⟨E.1,E.2.trans (by norm_num [cell12976])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy49 (n := 12976) (by norm_num)
        (q := 1 - (cell12976 ⟨49,by decide⟩).lower)
        (by norm_num [cell12976]) (by norm_num [cell12976])
      exact ⟨E.1,E.2.trans (by norm_num [cell12976])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy50 (n := 12976) (by norm_num)
        (q := 1 - (cell12976 ⟨50,by decide⟩).lower)
        (by norm_num [cell12976]) (by norm_num [cell12976])
      exact ⟨E.1,E.2.trans (by norm_num [cell12976])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy51 (n := 12976) (by norm_num)
        (q := 1 - (cell12976 ⟨51,by decide⟩).lower)
        (by norm_num [cell12976]) (by norm_num [cell12976])
      exact ⟨E.1,E.2.trans (by norm_num [cell12976])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy52 (n := 12976) (by norm_num)
        (q := 1 - (cell12976 ⟨52,by decide⟩).lower)
        (by norm_num [cell12976]) (by norm_num [cell12976])
      exact ⟨E.1,E.2.trans (by norm_num [cell12976])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12976

/-! Source-cell containment and simple scalar guards at 12976. -/
namespace BstLean.Part269.N12976
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12976)
open BstLean.Part268 (cell12976)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12976 ⟨10,by decide⟩).lower ∧ (cell12976 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12976 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12976 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12976 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12976 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12976 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12976,cell12976,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12976 ⟨11,by decide⟩).lower ∧ (cell12976 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12976 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12976 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12976 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12976 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12976 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12976,cell12976,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12976 ⟨12,by decide⟩).lower ∧ (cell12976 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12976 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12976 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12976 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12976 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12976 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12976,cell12976,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12976 ⟨13,by decide⟩).lower ∧ (cell12976 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12976 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12976 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12976 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12976 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12976 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12976,cell12976,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12976 ⟨14,by decide⟩).lower ∧ (cell12976 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12976 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12976 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12976 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12976 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12976 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12976,cell12976,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12976 ⟨15,by decide⟩).lower ∧ (cell12976 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12976 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12976 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12976 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12976 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12976 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12976,cell12976,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12976 ⟨16,by decide⟩).lower ∧ (cell12976 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12976 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12976 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12976 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12976 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12976 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12976,cell12976,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12976 ⟨17,by decide⟩).lower ∧ (cell12976 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12976 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12976 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12976 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12976 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12976 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12976,cell12976,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12976 ⟨18,by decide⟩).lower ∧ (cell12976 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12976 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12976 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12976 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12976 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12976 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12976,cell12976,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12976 ⟨19,by decide⟩).lower ∧ (cell12976 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12976 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12976 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12976 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12976 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12976 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12976,cell12976,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12976 ⟨20,by decide⟩).lower ∧ (cell12976 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12976 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12976 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12976 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12976 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12976 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12976,cell12976,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12976 ⟨21,by decide⟩).lower ∧ (cell12976 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12976 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12976 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12976 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12976 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12976 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12976,cell12976,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12976 ⟨22,by decide⟩).lower ∧ (cell12976 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12976 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12976 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12976 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12976 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12976 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12976,cell12976,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12976 ⟨23,by decide⟩).lower ∧ (cell12976 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12976 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12976 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12976 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12976 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12976 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12976,cell12976,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12976 ⟨24,by decide⟩).lower ∧ (cell12976 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12976 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12976 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12976 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12976 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12976 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12976,cell12976,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12976 ⟨25,by decide⟩).lower ∧ (cell12976 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12976 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12976 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12976 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12976 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12976 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12976,cell12976,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12976 ⟨26,by decide⟩).lower ∧ (cell12976 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12976 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12976 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12976 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12976 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12976 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12976,cell12976,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12976 ⟨27,by decide⟩).lower ∧ (cell12976 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12976 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12976 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12976 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12976 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12976 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12976,cell12976,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12976 ⟨28,by decide⟩).lower ∧ (cell12976 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12976 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12976 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12976 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12976 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12976 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12976,cell12976,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12976 ⟨29,by decide⟩).lower ∧ (cell12976 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12976 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12976 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12976 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12976 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12976 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12976,cell12976,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12976 ⟨30,by decide⟩).lower ∧ (cell12976 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12976 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12976 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12976 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12976 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12976 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12976,cell12976,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12976 ⟨31,by decide⟩).lower ∧ (cell12976 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12976 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12976 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12976 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12976 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12976 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12976,cell12976,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12976 ⟨32,by decide⟩).lower ∧ (cell12976 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12976 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12976 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12976 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12976 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12976 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12976,cell12976,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12976 ⟨33,by decide⟩).lower ∧ (cell12976 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12976 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12976 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12976 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12976 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12976 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12976,cell12976,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12976 ⟨34,by decide⟩).lower ∧ (cell12976 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12976 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12976 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12976 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12976 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12976 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12976,cell12976,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12976 ⟨35,by decide⟩).lower ∧ (cell12976 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12976 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12976 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12976 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12976 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12976 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12976,cell12976,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12976 ⟨36,by decide⟩).lower ∧ (cell12976 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12976 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12976 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12976 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12976 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12976 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12976,cell12976,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12976 ⟨37,by decide⟩).lower ∧ (cell12976 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12976 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12976 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12976 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12976 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12976 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12976,cell12976,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12976 ⟨38,by decide⟩).lower ∧ (cell12976 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12976 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12976 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12976 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12976 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12976 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12976,cell12976,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12976 ⟨39,by decide⟩).lower ∧ (cell12976 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12976 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12976 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12976 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12976 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12976 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12976,cell12976,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12976 ⟨40,by decide⟩).lower ∧ (cell12976 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12976 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12976 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12976 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12976 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12976 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12976,cell12976,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12976 ⟨41,by decide⟩).lower ∧ (cell12976 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12976 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12976 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12976 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12976 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12976 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12976,cell12976,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12976 ⟨42,by decide⟩).lower ∧ (cell12976 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12976 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12976 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12976 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12976 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12976 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12976,cell12976,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12976 ⟨43,by decide⟩).lower ∧ (cell12976 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12976 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12976 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12976 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12976 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12976 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12976,cell12976,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12976 ⟨44,by decide⟩).lower ∧ (cell12976 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12976 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12976 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12976 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12976 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12976 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12976,cell12976,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12976 ⟨45,by decide⟩).lower ∧ (cell12976 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12976 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12976 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12976 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12976 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12976 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12976,cell12976,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12976 ⟨46,by decide⟩).lower ∧ (cell12976 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12976 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12976 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12976 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12976 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12976 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12976,cell12976,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12976 ⟨47,by decide⟩).lower ∧ (cell12976 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12976 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12976 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12976 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12976 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12976 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12976,cell12976,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12976 ⟨48,by decide⟩).lower ∧ (cell12976 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12976 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12976 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12976 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12976 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12976 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12976,cell12976,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12976 ⟨49,by decide⟩).lower ∧ (cell12976 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12976 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12976 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12976 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12976 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12976 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12976,cell12976,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12976 ⟨50,by decide⟩).lower ∧ (cell12976 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12976 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12976 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12976 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12976 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12976 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12976,cell12976,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12976 ⟨51,by decide⟩).lower ∧ (cell12976 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12976 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12976 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12976 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12976 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12976 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12976,cell12976,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12976 ⟨52,by decide⟩).lower ∧ (cell12976 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12976 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12976 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12976 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12976 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12976 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12976,cell12976,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12976 i).lower ∧
    (cell12976 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12976 i).upper ≤ (0.532 : ℝ) ∧
    (cell12976 i).centre ≤ (0.1 : ℝ) ∧ (cell12976 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12976 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12976 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12976

/-! The local source numeric instances at 12976 have no network premises. -/
namespace BstLean.Part269.N12976
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12976)
open BstLean.Part268 (cell12976)

noncomputable def sourceNumerics12976 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12976 (cell12976 i)
      scalarRow12976.M scalarRow12976.H scalarRow12976.xi := by
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
    energy_allowance := scalarRow12976.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12976]
    centre_nonneg := (scalarRow12976.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D25.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12976])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12976
/-! Actual 12977 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12977
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12977 ≤ (1.035421634026 : ℝ) := by
  have hr : (113.916636186291 : ℝ) ≤ √(12977 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.916636186291 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12977 12977 (11 / 1000) ≤
    (0.008391109347 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12977) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.916636186291 : ℝ) ≤ √(12977 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12977)
  have hdiv : K / √(12977 : ℝ) ≤ K / 113.916636186291 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.916636186291 ≤ (0.008391109347 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12977.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12977 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12977 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12977 := gPlus_lower 12977
end BstLean.Part269.N12977

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12977
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035421634025 : ℝ) ≤ wn 12977 := by
  have hn : √(12977 : ℝ) ≤ 113.916636186292 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12977 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.916636186292 ≤ 2 / √(12977 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000246412118 : ℝ) ≤ rhoBar 12977 BstLean.Part154.csC ∧
    rhoBar 12977 BstLean.Part154.csC ≤ 0.000246412499 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035421634025 : ℝ) / (1.295212 * 12977) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035421634026 : ℝ) / (1.29521 * 12977) := by gcongr
      _ ≤ (0.000246412499 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12977 BstLean.Part154.csC) ≤ 0.000985710716 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12977 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12977 BstLean.Part154.csC) (piBar (rhoBar 12977 BstLean.Part154.csC)) ≤ 0.000188211339 ∧
    cc1 (rhoBar 12977 BstLean.Part154.csC) (piBar (rhoBar 12977 BstLean.Part154.csC)) ≤ 0.000119760164 ∧
    cc2 (rhoBar 12977 BstLean.Part154.csC) ≤ 0.000069521740 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12977 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12977 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12977 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12977 BstLean.Part154.csC * nuR (rhoBar 12977 BstLean.Part154.csC)) ≤ 0.000492840178 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000246412499 : ℝ) * 0.000985710716 := by gcongr
      _ ≤ (0.000492840178 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12977 BstLean.Part154.csC) * nuR (rhoBar 12977 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000985710716 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12977 BstLean.Part154.csC) * rhoBar 12977 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000246412499 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000246412499 / 2 + 0.399 * 0.000985710716 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000188211339 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000492840178 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119760164 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000246412499 / 1.414213562 := by gcongr
      _ ≤ (0.000069521740 : ℝ) := by norm_num

end BstLean.Part269.N12977

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12977
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12977 BstLean.Part154.csC) (piBar (rhoBar 12977 BstLean.Part154.csC)) ≤ 1.52977E-7 := by
  have hr0 : 0 ≤ rhoBar 12977 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12977 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12977 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12977 BstLean.Part154.csC) (piBar (rhoBar 12977 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12977 BstLean.Part154.csC) (piBar (rhoBar 12977 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12977 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000188211339 : ℝ) ^ 2 + 0.000119760164 ^ 2 + 3 * 0.000069521740 ^ 2 +
        2 * 0.797885 * 0.000188211339 * 0.000119760164 + 2 * 0.000188211339 * 0.000069521740 +
        4 * 0.797885 * 0.000119760164 * 0.000069521740 := by gcongr
    _ ≤ (1.52977E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12977 BstLean.Part154.csC Θ ≤ 0.002571232237 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12977 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12977 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12977 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12977 BstLean.Part154.csC) (piBar (rhoBar 12977 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12977 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035421634026 * 1.52977E-7 / (0.000246412118 : ℝ) := by gcongr
    _ ≤ 0.002571232237 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12977 BstLean.Part154.csC Θ ≤ 0.002851858402 + 0.000649710930 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12977 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12977 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12977 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035421634026 : ℝ) * ((2 * Θ * 0.000246412499 +
        (6863 / 10000) * 0.000246412499 * 12977 * 0.000985710716) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002851858402 + 0.000649710930 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12977 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12977 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12977 0.011 Θ ∧ gammaRatio 12977 0.011 Θ ≤ 0.000084710245 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12977 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035421634026 : ℝ) * 0.525 / ((1 - 0.011) * 12977) := by gcongr
      _ ≤ (0.000084710245 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12977 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12977 0.011 Θ) :=
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
    badAllowance 12977 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000421835223 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12977 BstLean.Part154.csC) 1.22 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 2 (rhoBar 12977 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12977 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12977 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12977 0.011 Θ) 1.12 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 1 (gammaRatio 12977 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12977 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12977 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12977 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12977 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035421634026 : ℝ) * 12977 *
        (1.5230E-8 / 1.1045361 + 1.8602E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000421835223 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12977 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003273693625 + 0.003220943167 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12977

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12977
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12977 BstLean.Part154.csC) (piBar (rhoBar 12977 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12977 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12977 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12977 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12977 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12977 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12977 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12977 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12977 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12977 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12977 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12977 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12977 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12977 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12977 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051915099253 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12977) ≤ 0.010483434388 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12977 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035421634026)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010483434388 + 2 * 0.737676 / 12977) := by gcongr
    _ ≤ (0.051915099253 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12977 12 ≤ 0.0015 := by
  exact BstLean.Part269.S25.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12977

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12977
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560515827664 : ℝ) ≤ plow 12977 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12977) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052471288788)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001349896925) : eMP 12977 0.011 xi bn ≤ 0.001162505455 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12977 : ℝ) * (1 - 0.011))) ≤ 0.000574830716 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001349896925 / (12977 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000574830716 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000574830716 : ℝ) + 3.141593 * 0.052471288788 / (12977 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001162505455 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052471288788)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001349896925) : PiBarMP 12977 12 0.011 xi bn ≤ 0.159503557232 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12977 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036740943442 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.288362156048 : ℝ) ≤ √((12977 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.916636186291 : ℝ) ≤ √(12977 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12977) ≤ 0.122303543444 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036740943442 + 0.052471288788 * 1.772454 / (2 * (113.288362156048 : ℝ))) * (1 + 0.001162505455) +
        8 / (12977 * 113.916636186291) + 0.122303543444 := by gcongr
    _ ≤ (0.159503557232 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052471288788)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001349896925) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280981222432) :
    parallelOracle 12977 0.011 xi bn cd ≤ 0.160472734403 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12977 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12977 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560515827664 : ℝ) ≤ plow 12977 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.916636186291 : ℝ) ≤ √(12977 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280981222432 : ℝ) / (2 * 0.560515827664 * 113.916636186291)) * 0.159503557232 +
        0.280981222432 ^ 2 / (2 * 0.560515827664 * 113.916636186291) := by gcongr
    _ ≤ (0.160472734403 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052471288788) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001349896925)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280981222432) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12977 12977 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560515827664 : ℝ) ≤ plow 12977 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.916636186291 : ℝ) ≤ √(12977 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12977 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12977 Θ 1.22 ≤ 0.011640973123 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.916636186291 := by gcongr <;> linarith
      _ ≤ (0.011640973123 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12977 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12977 12977 0.011 ≤ 0.008391109347 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12977 12977 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12977 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12977 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12977 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12977 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160472734403 + 0.011640973123 + (0.008391109347 : ℝ) *
        (1 + 2 * (0.280981222432 + 0.011640973123) / (0.560515827664 * 113.916636186291))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12977]

end BstLean.Part269.N12977

/-! The original eight local profiles supply actual 12977 moment certificates. -/
namespace BstLean.Part269.N12977
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12977 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12977 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12977 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052471288788 ∧
    0 ≤ bN 12977 BstLean.Part154.csC (groupTheta g) ∧ bN 12977 BstLean.Part154.csC (groupTheta g) ≤ 0.001349896925 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12977 12977 0.011
      (momentAllowance 12977 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12977 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12977 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12977 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12977 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12977 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229066123179 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12977 0.011
      (momentAllowance 12977 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12977 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12977
/-! The actual computed-centre upper energy formula at 12977. -/
namespace BstLean.Part269.N12977
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12977

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12977
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12977)
open BstLean.Part268 (cell12977)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084720558106
  | 2 => 0.085650033975
  | 3 => 0.086575841683
  | 4 => 0.087498974274
  | 5 => 0.088420645441
  | 6 => 0.089342323862
  | 7 => 0.090265771063
  | 8 => 0.091193082908
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12977 12977 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12977 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003274156000 + 0.003221457154 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S25.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12977

/-! Actual upper energy certificates on all 43 source endpoints at 12977. -/
namespace BstLean.Part269.N12977
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12977)
open BstLean.Part268 (cell12977)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12977 (gMinus 12977) (1 - (cell12977 i).lower) ≤ 1 ∧
    energyUpper 12977 (gMinus 12977) (BstLean.Part211.gPlus 12977)
      (finiteEnergy 12977 12977 0.011) (1 - (cell12977 i).lower) ≤
      (cell12977 i).energy := by
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
      have E := BstLean.Part269.S25.uniformEnergy10 (n := 12977) (by norm_num)
        (q := 1 - (cell12977 ⟨10,by decide⟩).lower)
        (by norm_num [cell12977]) (by norm_num [cell12977])
      exact ⟨E.1,E.2.trans (by norm_num [cell12977])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy11 (n := 12977) (by norm_num)
        (q := 1 - (cell12977 ⟨11,by decide⟩).lower)
        (by norm_num [cell12977]) (by norm_num [cell12977])
      exact ⟨E.1,E.2.trans (by norm_num [cell12977])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy12 (n := 12977) (by norm_num)
        (q := 1 - (cell12977 ⟨12,by decide⟩).lower)
        (by norm_num [cell12977]) (by norm_num [cell12977])
      exact ⟨E.1,E.2.trans (by norm_num [cell12977])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy13 (n := 12977) (by norm_num)
        (q := 1 - (cell12977 ⟨13,by decide⟩).lower)
        (by norm_num [cell12977]) (by norm_num [cell12977])
      exact ⟨E.1,E.2.trans (by norm_num [cell12977])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy14 (n := 12977) (by norm_num)
        (q := 1 - (cell12977 ⟨14,by decide⟩).lower)
        (by norm_num [cell12977]) (by norm_num [cell12977])
      exact ⟨E.1,E.2.trans (by norm_num [cell12977])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy15 (n := 12977) (by norm_num)
        (q := 1 - (cell12977 ⟨15,by decide⟩).lower)
        (by norm_num [cell12977]) (by norm_num [cell12977])
      exact ⟨E.1,E.2.trans (by norm_num [cell12977])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy16 (n := 12977) (by norm_num)
        (q := 1 - (cell12977 ⟨16,by decide⟩).lower)
        (by norm_num [cell12977]) (by norm_num [cell12977])
      exact ⟨E.1,E.2.trans (by norm_num [cell12977])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy17 (n := 12977) (by norm_num)
        (q := 1 - (cell12977 ⟨17,by decide⟩).lower)
        (by norm_num [cell12977]) (by norm_num [cell12977])
      exact ⟨E.1,E.2.trans (by norm_num [cell12977])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy18 (n := 12977) (by norm_num)
        (q := 1 - (cell12977 ⟨18,by decide⟩).lower)
        (by norm_num [cell12977]) (by norm_num [cell12977])
      exact ⟨E.1,E.2.trans (by norm_num [cell12977])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy19 (n := 12977) (by norm_num)
        (q := 1 - (cell12977 ⟨19,by decide⟩).lower)
        (by norm_num [cell12977]) (by norm_num [cell12977])
      exact ⟨E.1,E.2.trans (by norm_num [cell12977])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy20 (n := 12977) (by norm_num)
        (q := 1 - (cell12977 ⟨20,by decide⟩).lower)
        (by norm_num [cell12977]) (by norm_num [cell12977])
      exact ⟨E.1,E.2.trans (by norm_num [cell12977])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy21 (n := 12977) (by norm_num)
        (q := 1 - (cell12977 ⟨21,by decide⟩).lower)
        (by norm_num [cell12977]) (by norm_num [cell12977])
      exact ⟨E.1,E.2.trans (by norm_num [cell12977])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy22 (n := 12977) (by norm_num)
        (q := 1 - (cell12977 ⟨22,by decide⟩).lower)
        (by norm_num [cell12977]) (by norm_num [cell12977])
      exact ⟨E.1,E.2.trans (by norm_num [cell12977])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy23 (n := 12977) (by norm_num)
        (q := 1 - (cell12977 ⟨23,by decide⟩).lower)
        (by norm_num [cell12977]) (by norm_num [cell12977])
      exact ⟨E.1,E.2.trans (by norm_num [cell12977])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy24 (n := 12977) (by norm_num)
        (q := 1 - (cell12977 ⟨24,by decide⟩).lower)
        (by norm_num [cell12977]) (by norm_num [cell12977])
      exact ⟨E.1,E.2.trans (by norm_num [cell12977])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy25 (n := 12977) (by norm_num)
        (q := 1 - (cell12977 ⟨25,by decide⟩).lower)
        (by norm_num [cell12977]) (by norm_num [cell12977])
      exact ⟨E.1,E.2.trans (by norm_num [cell12977])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy26 (n := 12977) (by norm_num)
        (q := 1 - (cell12977 ⟨26,by decide⟩).lower)
        (by norm_num [cell12977]) (by norm_num [cell12977])
      exact ⟨E.1,E.2.trans (by norm_num [cell12977])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy27 (n := 12977) (by norm_num)
        (q := 1 - (cell12977 ⟨27,by decide⟩).lower)
        (by norm_num [cell12977]) (by norm_num [cell12977])
      exact ⟨E.1,E.2.trans (by norm_num [cell12977])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy28 (n := 12977) (by norm_num)
        (q := 1 - (cell12977 ⟨28,by decide⟩).lower)
        (by norm_num [cell12977]) (by norm_num [cell12977])
      exact ⟨E.1,E.2.trans (by norm_num [cell12977])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy29 (n := 12977) (by norm_num)
        (q := 1 - (cell12977 ⟨29,by decide⟩).lower)
        (by norm_num [cell12977]) (by norm_num [cell12977])
      exact ⟨E.1,E.2.trans (by norm_num [cell12977])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy30 (n := 12977) (by norm_num)
        (q := 1 - (cell12977 ⟨30,by decide⟩).lower)
        (by norm_num [cell12977]) (by norm_num [cell12977])
      exact ⟨E.1,E.2.trans (by norm_num [cell12977])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy31 (n := 12977) (by norm_num)
        (q := 1 - (cell12977 ⟨31,by decide⟩).lower)
        (by norm_num [cell12977]) (by norm_num [cell12977])
      exact ⟨E.1,E.2.trans (by norm_num [cell12977])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy32 (n := 12977) (by norm_num)
        (q := 1 - (cell12977 ⟨32,by decide⟩).lower)
        (by norm_num [cell12977]) (by norm_num [cell12977])
      exact ⟨E.1,E.2.trans (by norm_num [cell12977])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy33 (n := 12977) (by norm_num)
        (q := 1 - (cell12977 ⟨33,by decide⟩).lower)
        (by norm_num [cell12977]) (by norm_num [cell12977])
      exact ⟨E.1,E.2.trans (by norm_num [cell12977])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy34 (n := 12977) (by norm_num)
        (q := 1 - (cell12977 ⟨34,by decide⟩).lower)
        (by norm_num [cell12977]) (by norm_num [cell12977])
      exact ⟨E.1,E.2.trans (by norm_num [cell12977])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy35 (n := 12977) (by norm_num)
        (q := 1 - (cell12977 ⟨35,by decide⟩).lower)
        (by norm_num [cell12977]) (by norm_num [cell12977])
      exact ⟨E.1,E.2.trans (by norm_num [cell12977])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy36 (n := 12977) (by norm_num)
        (q := 1 - (cell12977 ⟨36,by decide⟩).lower)
        (by norm_num [cell12977]) (by norm_num [cell12977])
      exact ⟨E.1,E.2.trans (by norm_num [cell12977])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy37 (n := 12977) (by norm_num)
        (q := 1 - (cell12977 ⟨37,by decide⟩).lower)
        (by norm_num [cell12977]) (by norm_num [cell12977])
      exact ⟨E.1,E.2.trans (by norm_num [cell12977])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy38 (n := 12977) (by norm_num)
        (q := 1 - (cell12977 ⟨38,by decide⟩).lower)
        (by norm_num [cell12977]) (by norm_num [cell12977])
      exact ⟨E.1,E.2.trans (by norm_num [cell12977])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy39 (n := 12977) (by norm_num)
        (q := 1 - (cell12977 ⟨39,by decide⟩).lower)
        (by norm_num [cell12977]) (by norm_num [cell12977])
      exact ⟨E.1,E.2.trans (by norm_num [cell12977])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy40 (n := 12977) (by norm_num)
        (q := 1 - (cell12977 ⟨40,by decide⟩).lower)
        (by norm_num [cell12977]) (by norm_num [cell12977])
      exact ⟨E.1,E.2.trans (by norm_num [cell12977])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy41 (n := 12977) (by norm_num)
        (q := 1 - (cell12977 ⟨41,by decide⟩).lower)
        (by norm_num [cell12977]) (by norm_num [cell12977])
      exact ⟨E.1,E.2.trans (by norm_num [cell12977])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy42 (n := 12977) (by norm_num)
        (q := 1 - (cell12977 ⟨42,by decide⟩).lower)
        (by norm_num [cell12977]) (by norm_num [cell12977])
      exact ⟨E.1,E.2.trans (by norm_num [cell12977])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy43 (n := 12977) (by norm_num)
        (q := 1 - (cell12977 ⟨43,by decide⟩).lower)
        (by norm_num [cell12977]) (by norm_num [cell12977])
      exact ⟨E.1,E.2.trans (by norm_num [cell12977])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy44 (n := 12977) (by norm_num)
        (q := 1 - (cell12977 ⟨44,by decide⟩).lower)
        (by norm_num [cell12977]) (by norm_num [cell12977])
      exact ⟨E.1,E.2.trans (by norm_num [cell12977])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy45 (n := 12977) (by norm_num)
        (q := 1 - (cell12977 ⟨45,by decide⟩).lower)
        (by norm_num [cell12977]) (by norm_num [cell12977])
      exact ⟨E.1,E.2.trans (by norm_num [cell12977])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy46 (n := 12977) (by norm_num)
        (q := 1 - (cell12977 ⟨46,by decide⟩).lower)
        (by norm_num [cell12977]) (by norm_num [cell12977])
      exact ⟨E.1,E.2.trans (by norm_num [cell12977])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy47 (n := 12977) (by norm_num)
        (q := 1 - (cell12977 ⟨47,by decide⟩).lower)
        (by norm_num [cell12977]) (by norm_num [cell12977])
      exact ⟨E.1,E.2.trans (by norm_num [cell12977])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy48 (n := 12977) (by norm_num)
        (q := 1 - (cell12977 ⟨48,by decide⟩).lower)
        (by norm_num [cell12977]) (by norm_num [cell12977])
      exact ⟨E.1,E.2.trans (by norm_num [cell12977])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy49 (n := 12977) (by norm_num)
        (q := 1 - (cell12977 ⟨49,by decide⟩).lower)
        (by norm_num [cell12977]) (by norm_num [cell12977])
      exact ⟨E.1,E.2.trans (by norm_num [cell12977])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy50 (n := 12977) (by norm_num)
        (q := 1 - (cell12977 ⟨50,by decide⟩).lower)
        (by norm_num [cell12977]) (by norm_num [cell12977])
      exact ⟨E.1,E.2.trans (by norm_num [cell12977])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy51 (n := 12977) (by norm_num)
        (q := 1 - (cell12977 ⟨51,by decide⟩).lower)
        (by norm_num [cell12977]) (by norm_num [cell12977])
      exact ⟨E.1,E.2.trans (by norm_num [cell12977])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy52 (n := 12977) (by norm_num)
        (q := 1 - (cell12977 ⟨52,by decide⟩).lower)
        (by norm_num [cell12977]) (by norm_num [cell12977])
      exact ⟨E.1,E.2.trans (by norm_num [cell12977])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12977

/-! Source-cell containment and simple scalar guards at 12977. -/
namespace BstLean.Part269.N12977
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12977)
open BstLean.Part268 (cell12977)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12977 ⟨10,by decide⟩).lower ∧ (cell12977 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12977 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12977 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12977 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12977 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12977 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12977,cell12977,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12977 ⟨11,by decide⟩).lower ∧ (cell12977 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12977 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12977 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12977 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12977 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12977 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12977,cell12977,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12977 ⟨12,by decide⟩).lower ∧ (cell12977 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12977 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12977 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12977 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12977 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12977 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12977,cell12977,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12977 ⟨13,by decide⟩).lower ∧ (cell12977 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12977 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12977 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12977 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12977 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12977 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12977,cell12977,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12977 ⟨14,by decide⟩).lower ∧ (cell12977 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12977 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12977 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12977 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12977 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12977 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12977,cell12977,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12977 ⟨15,by decide⟩).lower ∧ (cell12977 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12977 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12977 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12977 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12977 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12977 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12977,cell12977,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12977 ⟨16,by decide⟩).lower ∧ (cell12977 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12977 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12977 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12977 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12977 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12977 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12977,cell12977,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12977 ⟨17,by decide⟩).lower ∧ (cell12977 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12977 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12977 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12977 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12977 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12977 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12977,cell12977,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12977 ⟨18,by decide⟩).lower ∧ (cell12977 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12977 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12977 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12977 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12977 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12977 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12977,cell12977,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12977 ⟨19,by decide⟩).lower ∧ (cell12977 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12977 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12977 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12977 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12977 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12977 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12977,cell12977,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12977 ⟨20,by decide⟩).lower ∧ (cell12977 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12977 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12977 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12977 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12977 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12977 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12977,cell12977,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12977 ⟨21,by decide⟩).lower ∧ (cell12977 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12977 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12977 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12977 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12977 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12977 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12977,cell12977,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12977 ⟨22,by decide⟩).lower ∧ (cell12977 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12977 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12977 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12977 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12977 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12977 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12977,cell12977,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12977 ⟨23,by decide⟩).lower ∧ (cell12977 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12977 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12977 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12977 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12977 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12977 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12977,cell12977,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12977 ⟨24,by decide⟩).lower ∧ (cell12977 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12977 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12977 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12977 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12977 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12977 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12977,cell12977,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12977 ⟨25,by decide⟩).lower ∧ (cell12977 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12977 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12977 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12977 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12977 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12977 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12977,cell12977,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12977 ⟨26,by decide⟩).lower ∧ (cell12977 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12977 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12977 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12977 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12977 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12977 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12977,cell12977,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12977 ⟨27,by decide⟩).lower ∧ (cell12977 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12977 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12977 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12977 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12977 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12977 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12977,cell12977,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12977 ⟨28,by decide⟩).lower ∧ (cell12977 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12977 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12977 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12977 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12977 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12977 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12977,cell12977,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12977 ⟨29,by decide⟩).lower ∧ (cell12977 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12977 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12977 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12977 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12977 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12977 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12977,cell12977,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12977 ⟨30,by decide⟩).lower ∧ (cell12977 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12977 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12977 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12977 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12977 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12977 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12977,cell12977,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12977 ⟨31,by decide⟩).lower ∧ (cell12977 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12977 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12977 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12977 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12977 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12977 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12977,cell12977,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12977 ⟨32,by decide⟩).lower ∧ (cell12977 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12977 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12977 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12977 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12977 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12977 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12977,cell12977,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12977 ⟨33,by decide⟩).lower ∧ (cell12977 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12977 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12977 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12977 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12977 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12977 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12977,cell12977,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12977 ⟨34,by decide⟩).lower ∧ (cell12977 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12977 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12977 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12977 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12977 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12977 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12977,cell12977,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12977 ⟨35,by decide⟩).lower ∧ (cell12977 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12977 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12977 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12977 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12977 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12977 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12977,cell12977,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12977 ⟨36,by decide⟩).lower ∧ (cell12977 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12977 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12977 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12977 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12977 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12977 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12977,cell12977,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12977 ⟨37,by decide⟩).lower ∧ (cell12977 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12977 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12977 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12977 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12977 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12977 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12977,cell12977,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12977 ⟨38,by decide⟩).lower ∧ (cell12977 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12977 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12977 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12977 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12977 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12977 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12977,cell12977,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12977 ⟨39,by decide⟩).lower ∧ (cell12977 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12977 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12977 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12977 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12977 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12977 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12977,cell12977,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12977 ⟨40,by decide⟩).lower ∧ (cell12977 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12977 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12977 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12977 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12977 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12977 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12977,cell12977,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12977 ⟨41,by decide⟩).lower ∧ (cell12977 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12977 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12977 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12977 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12977 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12977 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12977,cell12977,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12977 ⟨42,by decide⟩).lower ∧ (cell12977 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12977 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12977 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12977 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12977 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12977 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12977,cell12977,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12977 ⟨43,by decide⟩).lower ∧ (cell12977 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12977 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12977 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12977 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12977 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12977 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12977,cell12977,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12977 ⟨44,by decide⟩).lower ∧ (cell12977 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12977 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12977 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12977 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12977 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12977 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12977,cell12977,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12977 ⟨45,by decide⟩).lower ∧ (cell12977 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12977 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12977 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12977 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12977 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12977 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12977,cell12977,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12977 ⟨46,by decide⟩).lower ∧ (cell12977 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12977 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12977 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12977 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12977 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12977 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12977,cell12977,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12977 ⟨47,by decide⟩).lower ∧ (cell12977 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12977 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12977 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12977 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12977 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12977 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12977,cell12977,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12977 ⟨48,by decide⟩).lower ∧ (cell12977 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12977 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12977 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12977 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12977 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12977 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12977,cell12977,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12977 ⟨49,by decide⟩).lower ∧ (cell12977 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12977 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12977 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12977 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12977 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12977 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12977,cell12977,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12977 ⟨50,by decide⟩).lower ∧ (cell12977 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12977 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12977 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12977 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12977 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12977 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12977,cell12977,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12977 ⟨51,by decide⟩).lower ∧ (cell12977 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12977 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12977 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12977 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12977 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12977 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12977,cell12977,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12977 ⟨52,by decide⟩).lower ∧ (cell12977 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12977 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12977 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12977 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12977 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12977 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12977,cell12977,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12977 i).lower ∧
    (cell12977 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12977 i).upper ≤ (0.532 : ℝ) ∧
    (cell12977 i).centre ≤ (0.1 : ℝ) ∧ (cell12977 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12977 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12977 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12977

/-! The local source numeric instances at 12977 have no network premises. -/
namespace BstLean.Part269.N12977
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12977)
open BstLean.Part268 (cell12977)

noncomputable def sourceNumerics12977 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12977 (cell12977 i)
      scalarRow12977.M scalarRow12977.H scalarRow12977.xi := by
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
    energy_allowance := scalarRow12977.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12977]
    centre_nonneg := (scalarRow12977.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D25.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12977])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12977
/-! Actual 12978 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12978
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12978 ≤ (1.035420257444 : ℝ) := by
  have hr : (113.921025276285 : ℝ) ≤ √(12978 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.921025276285 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12978 12978 (11 / 1000) ≤
    (0.008390786056 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12978) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.921025276285 : ℝ) ≤ √(12978 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12978)
  have hdiv : K / √(12978 : ℝ) ≤ K / 113.921025276285 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.921025276285 ≤ (0.008390786056 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12978.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12978 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12978 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12978 := gPlus_lower 12978
end BstLean.Part269.N12978

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12978
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035420257443 : ℝ) ≤ wn 12978 := by
  have hn : √(12978 : ℝ) ≤ 113.921025276286 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12978 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.921025276286 ≤ 2 / √(12978 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000246392803 : ℝ) ≤ rhoBar 12978 BstLean.Part154.csC ∧
    rhoBar 12978 BstLean.Part154.csC ≤ 0.000246393185 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035420257443 : ℝ) / (1.295212 * 12978) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035420257444 : ℝ) / (1.29521 * 12978) := by gcongr
      _ ≤ (0.000246393185 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12978 BstLean.Part154.csC) ≤ 0.000985633450 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12978 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12978 BstLean.Part154.csC) (piBar (rhoBar 12978 BstLean.Part154.csC)) ≤ 0.000188196586 ∧
    cc1 (rhoBar 12978 BstLean.Part154.csC) (piBar (rhoBar 12978 BstLean.Part154.csC)) ≤ 0.000119750777 ∧
    cc2 (rhoBar 12978 BstLean.Part154.csC) ≤ 0.000069516291 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12978 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12978 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12978 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12978 BstLean.Part154.csC * nuR (rhoBar 12978 BstLean.Part154.csC)) ≤ 0.000492801548 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000246393185 : ℝ) * 0.000985633450 := by gcongr
      _ ≤ (0.000492801548 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12978 BstLean.Part154.csC) * nuR (rhoBar 12978 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000985633450 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12978 BstLean.Part154.csC) * rhoBar 12978 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000246393185 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000246393185 / 2 + 0.399 * 0.000985633450 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000188196586 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000492801548 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119750777 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000246393185 / 1.414213562 := by gcongr
      _ ≤ (0.000069516291 : ℝ) := by norm_num

end BstLean.Part269.N12978

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12978
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12978 BstLean.Part154.csC) (piBar (rhoBar 12978 BstLean.Part154.csC)) ≤ 1.52953E-7 := by
  have hr0 : 0 ≤ rhoBar 12978 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12978 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12978 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12978 BstLean.Part154.csC) (piBar (rhoBar 12978 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12978 BstLean.Part154.csC) (piBar (rhoBar 12978 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12978 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000188196586 : ℝ) ^ 2 + 0.000119750777 ^ 2 + 3 * 0.000069516291 ^ 2 +
        2 * 0.797885 * 0.000188196586 * 0.000119750777 + 2 * 0.000188196586 * 0.000069516291 +
        4 * 0.797885 * 0.000119750777 * 0.000069516291 := by gcongr
    _ ≤ (1.52953E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12978 BstLean.Part154.csC Θ ≤ 0.002571026958 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12978 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12978 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12978 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12978 BstLean.Part154.csC) (piBar (rhoBar 12978 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12978 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035420257444 * 1.52953E-7 / (0.000246392803 : ℝ) := by gcongr
    _ ≤ 0.002571026958 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12978 BstLean.Part154.csC Θ ≤ 0.002851627280 + 0.000649659142 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12978 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12978 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12978 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035420257444 : ℝ) * ((2 * Θ * 0.000246393185 +
        (6863 / 10000) * 0.000246393185 * 12978 * 0.000985633450) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002851627280 + 0.000649659142 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12978 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12978 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12978 0.011 Θ ∧ gammaRatio 12978 0.011 Θ ≤ 0.000084703606 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12978 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035420257444 : ℝ) * 0.525 / ((1 - 0.011) * 12978) := by gcongr
      _ ≤ (0.000084703606 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12978 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12978 0.011 Θ) :=
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
    badAllowance 12978 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000421835223 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12978 BstLean.Part154.csC) 1.22 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 2 (rhoBar 12978 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12978 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12978 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12978 0.011 Θ) 1.12 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 1 (gammaRatio 12978 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12978 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12978 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12978 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12978 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035420257444 : ℝ) * 12978 *
        (1.5230E-8 / 1.1045361 + 1.8602E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000421835223 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12978 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003273462503 + 0.003220686100 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12978

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12978
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12978 BstLean.Part154.csC) (piBar (rhoBar 12978 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12978 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12978 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12978 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12978 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12978 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12978 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12978 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12978 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12978 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12978 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12978 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12978 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12978 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12978 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051913077634 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12978) ≤ 0.010483030487 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12978 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035420257444)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010483030487 + 2 * 0.737676 / 12978) := by gcongr
    _ ≤ (0.051913077634 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12978 12 ≤ 0.0015 := by
  exact BstLean.Part269.S25.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12978

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12978
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560515870973 : ℝ) ≤ plow 12978 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12978) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052470922706)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001349789153) : eMP 12978 0.011 xi bn ≤ 0.001162414190 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12978 : ℝ) * (1 - 0.011))) ≤ 0.000574785623 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001349789153 / (12978 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000574785623 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000574785623 : ℝ) + 3.141593 * 0.052470922706 / (12978 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001162414190 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052470922706)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001349789153) : PiBarMP 12978 12 0.011 xi bn ≤ 0.159497354089 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12978 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036739476766 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.292727039294 : ℝ) ≤ √((12978 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.921025276285 : ℝ) ≤ √(12978 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12978) ≤ 0.122298831397 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036739476766 + 0.052470922706 * 1.772454 / (2 * (113.292727039294 : ℝ))) * (1 + 0.001162414190) +
        8 / (12978 * 113.921025276285) + 0.122298831397 := by gcongr
    _ ≤ (0.159497354089 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052470922706)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001349789153) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280978401737) :
    parallelOracle 12978 0.011 xi bn cd ≤ 0.160466464263 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12978 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12978 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560515870973 : ℝ) ≤ plow 12978 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.921025276285 : ℝ) ≤ √(12978 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280978401737 : ℝ) / (2 * 0.560515870973 * 113.921025276285)) * 0.159497354089 +
        0.280978401737 ^ 2 / (2 * 0.560515870973 * 113.921025276285) := by gcongr
    _ ≤ (0.160466464263 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052470922706) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001349789153)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280978401737) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12978 12978 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560515870973 : ℝ) ≤ plow 12978 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.921025276285 : ℝ) ≤ √(12978 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12978 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12978 Θ 1.22 ≤ 0.011640524625 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.921025276285 := by gcongr <;> linarith
      _ ≤ (0.011640524625 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12978 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12978 12978 0.011 ≤ 0.008390786056 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12978 12978 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12978 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12978 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12978 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12978 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160466464263 + 0.011640524625 + (0.008390786056 : ℝ) *
        (1 + 2 * (0.280978401737 + 0.011640524625) / (0.560515870973 * 113.921025276285))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12978]

end BstLean.Part269.N12978

/-! The original eight local profiles supply actual 12978 moment certificates. -/
namespace BstLean.Part269.N12978
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12978 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12978 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12978 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052470922706 ∧
    0 ≤ bN 12978 BstLean.Part154.csC (groupTheta g) ∧ bN 12978 BstLean.Part154.csC (groupTheta g) ≤ 0.001349789153 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12978 12978 0.011
      (momentAllowance 12978 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12978 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12978 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12978 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12978 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12978 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229065324103 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12978 0.011
      (momentAllowance 12978 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12978 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12978
/-! The actual computed-centre upper energy formula at 12978. -/
namespace BstLean.Part269.N12978
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12978

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12978
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12978)
open BstLean.Part268 (cell12978)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084717921131
  | 2 => 0.085647361786
  | 3 => 0.086573128864
  | 4 => 0.087496214145
  | 5 => 0.088417829829
  | 6 => 0.089339442839
  | 7 => 0.090262812660
  | 8 => 0.091190032784
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12978 12978 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12978 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003274156000 + 0.003221457154 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S25.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12978

/-! Actual upper energy certificates on all 43 source endpoints at 12978. -/
namespace BstLean.Part269.N12978
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12978)
open BstLean.Part268 (cell12978)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12978 (gMinus 12978) (1 - (cell12978 i).lower) ≤ 1 ∧
    energyUpper 12978 (gMinus 12978) (BstLean.Part211.gPlus 12978)
      (finiteEnergy 12978 12978 0.011) (1 - (cell12978 i).lower) ≤
      (cell12978 i).energy := by
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
      have E := BstLean.Part269.S25.uniformEnergy10 (n := 12978) (by norm_num)
        (q := 1 - (cell12978 ⟨10,by decide⟩).lower)
        (by norm_num [cell12978]) (by norm_num [cell12978])
      exact ⟨E.1,E.2.trans (by norm_num [cell12978])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy11 (n := 12978) (by norm_num)
        (q := 1 - (cell12978 ⟨11,by decide⟩).lower)
        (by norm_num [cell12978]) (by norm_num [cell12978])
      exact ⟨E.1,E.2.trans (by norm_num [cell12978])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy12 (n := 12978) (by norm_num)
        (q := 1 - (cell12978 ⟨12,by decide⟩).lower)
        (by norm_num [cell12978]) (by norm_num [cell12978])
      exact ⟨E.1,E.2.trans (by norm_num [cell12978])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy13 (n := 12978) (by norm_num)
        (q := 1 - (cell12978 ⟨13,by decide⟩).lower)
        (by norm_num [cell12978]) (by norm_num [cell12978])
      exact ⟨E.1,E.2.trans (by norm_num [cell12978])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy14 (n := 12978) (by norm_num)
        (q := 1 - (cell12978 ⟨14,by decide⟩).lower)
        (by norm_num [cell12978]) (by norm_num [cell12978])
      exact ⟨E.1,E.2.trans (by norm_num [cell12978])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy15 (n := 12978) (by norm_num)
        (q := 1 - (cell12978 ⟨15,by decide⟩).lower)
        (by norm_num [cell12978]) (by norm_num [cell12978])
      exact ⟨E.1,E.2.trans (by norm_num [cell12978])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy16 (n := 12978) (by norm_num)
        (q := 1 - (cell12978 ⟨16,by decide⟩).lower)
        (by norm_num [cell12978]) (by norm_num [cell12978])
      exact ⟨E.1,E.2.trans (by norm_num [cell12978])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy17 (n := 12978) (by norm_num)
        (q := 1 - (cell12978 ⟨17,by decide⟩).lower)
        (by norm_num [cell12978]) (by norm_num [cell12978])
      exact ⟨E.1,E.2.trans (by norm_num [cell12978])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy18 (n := 12978) (by norm_num)
        (q := 1 - (cell12978 ⟨18,by decide⟩).lower)
        (by norm_num [cell12978]) (by norm_num [cell12978])
      exact ⟨E.1,E.2.trans (by norm_num [cell12978])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy19 (n := 12978) (by norm_num)
        (q := 1 - (cell12978 ⟨19,by decide⟩).lower)
        (by norm_num [cell12978]) (by norm_num [cell12978])
      exact ⟨E.1,E.2.trans (by norm_num [cell12978])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy20 (n := 12978) (by norm_num)
        (q := 1 - (cell12978 ⟨20,by decide⟩).lower)
        (by norm_num [cell12978]) (by norm_num [cell12978])
      exact ⟨E.1,E.2.trans (by norm_num [cell12978])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy21 (n := 12978) (by norm_num)
        (q := 1 - (cell12978 ⟨21,by decide⟩).lower)
        (by norm_num [cell12978]) (by norm_num [cell12978])
      exact ⟨E.1,E.2.trans (by norm_num [cell12978])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy22 (n := 12978) (by norm_num)
        (q := 1 - (cell12978 ⟨22,by decide⟩).lower)
        (by norm_num [cell12978]) (by norm_num [cell12978])
      exact ⟨E.1,E.2.trans (by norm_num [cell12978])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy23 (n := 12978) (by norm_num)
        (q := 1 - (cell12978 ⟨23,by decide⟩).lower)
        (by norm_num [cell12978]) (by norm_num [cell12978])
      exact ⟨E.1,E.2.trans (by norm_num [cell12978])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy24 (n := 12978) (by norm_num)
        (q := 1 - (cell12978 ⟨24,by decide⟩).lower)
        (by norm_num [cell12978]) (by norm_num [cell12978])
      exact ⟨E.1,E.2.trans (by norm_num [cell12978])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy25 (n := 12978) (by norm_num)
        (q := 1 - (cell12978 ⟨25,by decide⟩).lower)
        (by norm_num [cell12978]) (by norm_num [cell12978])
      exact ⟨E.1,E.2.trans (by norm_num [cell12978])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy26 (n := 12978) (by norm_num)
        (q := 1 - (cell12978 ⟨26,by decide⟩).lower)
        (by norm_num [cell12978]) (by norm_num [cell12978])
      exact ⟨E.1,E.2.trans (by norm_num [cell12978])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy27 (n := 12978) (by norm_num)
        (q := 1 - (cell12978 ⟨27,by decide⟩).lower)
        (by norm_num [cell12978]) (by norm_num [cell12978])
      exact ⟨E.1,E.2.trans (by norm_num [cell12978])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy28 (n := 12978) (by norm_num)
        (q := 1 - (cell12978 ⟨28,by decide⟩).lower)
        (by norm_num [cell12978]) (by norm_num [cell12978])
      exact ⟨E.1,E.2.trans (by norm_num [cell12978])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy29 (n := 12978) (by norm_num)
        (q := 1 - (cell12978 ⟨29,by decide⟩).lower)
        (by norm_num [cell12978]) (by norm_num [cell12978])
      exact ⟨E.1,E.2.trans (by norm_num [cell12978])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy30 (n := 12978) (by norm_num)
        (q := 1 - (cell12978 ⟨30,by decide⟩).lower)
        (by norm_num [cell12978]) (by norm_num [cell12978])
      exact ⟨E.1,E.2.trans (by norm_num [cell12978])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy31 (n := 12978) (by norm_num)
        (q := 1 - (cell12978 ⟨31,by decide⟩).lower)
        (by norm_num [cell12978]) (by norm_num [cell12978])
      exact ⟨E.1,E.2.trans (by norm_num [cell12978])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy32 (n := 12978) (by norm_num)
        (q := 1 - (cell12978 ⟨32,by decide⟩).lower)
        (by norm_num [cell12978]) (by norm_num [cell12978])
      exact ⟨E.1,E.2.trans (by norm_num [cell12978])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy33 (n := 12978) (by norm_num)
        (q := 1 - (cell12978 ⟨33,by decide⟩).lower)
        (by norm_num [cell12978]) (by norm_num [cell12978])
      exact ⟨E.1,E.2.trans (by norm_num [cell12978])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy34 (n := 12978) (by norm_num)
        (q := 1 - (cell12978 ⟨34,by decide⟩).lower)
        (by norm_num [cell12978]) (by norm_num [cell12978])
      exact ⟨E.1,E.2.trans (by norm_num [cell12978])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy35 (n := 12978) (by norm_num)
        (q := 1 - (cell12978 ⟨35,by decide⟩).lower)
        (by norm_num [cell12978]) (by norm_num [cell12978])
      exact ⟨E.1,E.2.trans (by norm_num [cell12978])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy36 (n := 12978) (by norm_num)
        (q := 1 - (cell12978 ⟨36,by decide⟩).lower)
        (by norm_num [cell12978]) (by norm_num [cell12978])
      exact ⟨E.1,E.2.trans (by norm_num [cell12978])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy37 (n := 12978) (by norm_num)
        (q := 1 - (cell12978 ⟨37,by decide⟩).lower)
        (by norm_num [cell12978]) (by norm_num [cell12978])
      exact ⟨E.1,E.2.trans (by norm_num [cell12978])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy38 (n := 12978) (by norm_num)
        (q := 1 - (cell12978 ⟨38,by decide⟩).lower)
        (by norm_num [cell12978]) (by norm_num [cell12978])
      exact ⟨E.1,E.2.trans (by norm_num [cell12978])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy39 (n := 12978) (by norm_num)
        (q := 1 - (cell12978 ⟨39,by decide⟩).lower)
        (by norm_num [cell12978]) (by norm_num [cell12978])
      exact ⟨E.1,E.2.trans (by norm_num [cell12978])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy40 (n := 12978) (by norm_num)
        (q := 1 - (cell12978 ⟨40,by decide⟩).lower)
        (by norm_num [cell12978]) (by norm_num [cell12978])
      exact ⟨E.1,E.2.trans (by norm_num [cell12978])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy41 (n := 12978) (by norm_num)
        (q := 1 - (cell12978 ⟨41,by decide⟩).lower)
        (by norm_num [cell12978]) (by norm_num [cell12978])
      exact ⟨E.1,E.2.trans (by norm_num [cell12978])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy42 (n := 12978) (by norm_num)
        (q := 1 - (cell12978 ⟨42,by decide⟩).lower)
        (by norm_num [cell12978]) (by norm_num [cell12978])
      exact ⟨E.1,E.2.trans (by norm_num [cell12978])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy43 (n := 12978) (by norm_num)
        (q := 1 - (cell12978 ⟨43,by decide⟩).lower)
        (by norm_num [cell12978]) (by norm_num [cell12978])
      exact ⟨E.1,E.2.trans (by norm_num [cell12978])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy44 (n := 12978) (by norm_num)
        (q := 1 - (cell12978 ⟨44,by decide⟩).lower)
        (by norm_num [cell12978]) (by norm_num [cell12978])
      exact ⟨E.1,E.2.trans (by norm_num [cell12978])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy45 (n := 12978) (by norm_num)
        (q := 1 - (cell12978 ⟨45,by decide⟩).lower)
        (by norm_num [cell12978]) (by norm_num [cell12978])
      exact ⟨E.1,E.2.trans (by norm_num [cell12978])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy46 (n := 12978) (by norm_num)
        (q := 1 - (cell12978 ⟨46,by decide⟩).lower)
        (by norm_num [cell12978]) (by norm_num [cell12978])
      exact ⟨E.1,E.2.trans (by norm_num [cell12978])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy47 (n := 12978) (by norm_num)
        (q := 1 - (cell12978 ⟨47,by decide⟩).lower)
        (by norm_num [cell12978]) (by norm_num [cell12978])
      exact ⟨E.1,E.2.trans (by norm_num [cell12978])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy48 (n := 12978) (by norm_num)
        (q := 1 - (cell12978 ⟨48,by decide⟩).lower)
        (by norm_num [cell12978]) (by norm_num [cell12978])
      exact ⟨E.1,E.2.trans (by norm_num [cell12978])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy49 (n := 12978) (by norm_num)
        (q := 1 - (cell12978 ⟨49,by decide⟩).lower)
        (by norm_num [cell12978]) (by norm_num [cell12978])
      exact ⟨E.1,E.2.trans (by norm_num [cell12978])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy50 (n := 12978) (by norm_num)
        (q := 1 - (cell12978 ⟨50,by decide⟩).lower)
        (by norm_num [cell12978]) (by norm_num [cell12978])
      exact ⟨E.1,E.2.trans (by norm_num [cell12978])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy51 (n := 12978) (by norm_num)
        (q := 1 - (cell12978 ⟨51,by decide⟩).lower)
        (by norm_num [cell12978]) (by norm_num [cell12978])
      exact ⟨E.1,E.2.trans (by norm_num [cell12978])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy52 (n := 12978) (by norm_num)
        (q := 1 - (cell12978 ⟨52,by decide⟩).lower)
        (by norm_num [cell12978]) (by norm_num [cell12978])
      exact ⟨E.1,E.2.trans (by norm_num [cell12978])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12978

/-! Source-cell containment and simple scalar guards at 12978. -/
namespace BstLean.Part269.N12978
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12978)
open BstLean.Part268 (cell12978)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12978 ⟨10,by decide⟩).lower ∧ (cell12978 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12978 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12978 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12978 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12978 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12978 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12978,cell12978,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12978 ⟨11,by decide⟩).lower ∧ (cell12978 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12978 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12978 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12978 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12978 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12978 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12978,cell12978,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12978 ⟨12,by decide⟩).lower ∧ (cell12978 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12978 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12978 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12978 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12978 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12978 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12978,cell12978,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12978 ⟨13,by decide⟩).lower ∧ (cell12978 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12978 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12978 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12978 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12978 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12978 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12978,cell12978,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12978 ⟨14,by decide⟩).lower ∧ (cell12978 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12978 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12978 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12978 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12978 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12978 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12978,cell12978,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12978 ⟨15,by decide⟩).lower ∧ (cell12978 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12978 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12978 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12978 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12978 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12978 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12978,cell12978,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12978 ⟨16,by decide⟩).lower ∧ (cell12978 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12978 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12978 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12978 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12978 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12978 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12978,cell12978,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12978 ⟨17,by decide⟩).lower ∧ (cell12978 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12978 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12978 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12978 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12978 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12978 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12978,cell12978,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12978 ⟨18,by decide⟩).lower ∧ (cell12978 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12978 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12978 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12978 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12978 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12978 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12978,cell12978,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12978 ⟨19,by decide⟩).lower ∧ (cell12978 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12978 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12978 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12978 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12978 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12978 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12978,cell12978,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12978 ⟨20,by decide⟩).lower ∧ (cell12978 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12978 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12978 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12978 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12978 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12978 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12978,cell12978,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12978 ⟨21,by decide⟩).lower ∧ (cell12978 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12978 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12978 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12978 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12978 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12978 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12978,cell12978,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12978 ⟨22,by decide⟩).lower ∧ (cell12978 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12978 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12978 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12978 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12978 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12978 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12978,cell12978,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12978 ⟨23,by decide⟩).lower ∧ (cell12978 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12978 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12978 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12978 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12978 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12978 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12978,cell12978,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12978 ⟨24,by decide⟩).lower ∧ (cell12978 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12978 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12978 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12978 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12978 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12978 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12978,cell12978,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12978 ⟨25,by decide⟩).lower ∧ (cell12978 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12978 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12978 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12978 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12978 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12978 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12978,cell12978,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12978 ⟨26,by decide⟩).lower ∧ (cell12978 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12978 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12978 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12978 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12978 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12978 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12978,cell12978,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12978 ⟨27,by decide⟩).lower ∧ (cell12978 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12978 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12978 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12978 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12978 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12978 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12978,cell12978,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12978 ⟨28,by decide⟩).lower ∧ (cell12978 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12978 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12978 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12978 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12978 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12978 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12978,cell12978,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12978 ⟨29,by decide⟩).lower ∧ (cell12978 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12978 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12978 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12978 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12978 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12978 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12978,cell12978,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12978 ⟨30,by decide⟩).lower ∧ (cell12978 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12978 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12978 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12978 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12978 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12978 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12978,cell12978,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12978 ⟨31,by decide⟩).lower ∧ (cell12978 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12978 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12978 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12978 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12978 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12978 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12978,cell12978,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12978 ⟨32,by decide⟩).lower ∧ (cell12978 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12978 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12978 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12978 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12978 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12978 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12978,cell12978,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12978 ⟨33,by decide⟩).lower ∧ (cell12978 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12978 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12978 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12978 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12978 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12978 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12978,cell12978,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12978 ⟨34,by decide⟩).lower ∧ (cell12978 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12978 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12978 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12978 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12978 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12978 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12978,cell12978,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12978 ⟨35,by decide⟩).lower ∧ (cell12978 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12978 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12978 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12978 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12978 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12978 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12978,cell12978,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12978 ⟨36,by decide⟩).lower ∧ (cell12978 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12978 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12978 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12978 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12978 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12978 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12978,cell12978,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12978 ⟨37,by decide⟩).lower ∧ (cell12978 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12978 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12978 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12978 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12978 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12978 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12978,cell12978,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12978 ⟨38,by decide⟩).lower ∧ (cell12978 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12978 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12978 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12978 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12978 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12978 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12978,cell12978,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12978 ⟨39,by decide⟩).lower ∧ (cell12978 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12978 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12978 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12978 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12978 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12978 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12978,cell12978,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12978 ⟨40,by decide⟩).lower ∧ (cell12978 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12978 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12978 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12978 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12978 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12978 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12978,cell12978,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12978 ⟨41,by decide⟩).lower ∧ (cell12978 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12978 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12978 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12978 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12978 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12978 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12978,cell12978,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12978 ⟨42,by decide⟩).lower ∧ (cell12978 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12978 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12978 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12978 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12978 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12978 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12978,cell12978,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12978 ⟨43,by decide⟩).lower ∧ (cell12978 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12978 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12978 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12978 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12978 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12978 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12978,cell12978,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12978 ⟨44,by decide⟩).lower ∧ (cell12978 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12978 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12978 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12978 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12978 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12978 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12978,cell12978,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12978 ⟨45,by decide⟩).lower ∧ (cell12978 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12978 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12978 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12978 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12978 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12978 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12978,cell12978,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12978 ⟨46,by decide⟩).lower ∧ (cell12978 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12978 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12978 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12978 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12978 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12978 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12978,cell12978,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12978 ⟨47,by decide⟩).lower ∧ (cell12978 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12978 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12978 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12978 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12978 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12978 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12978,cell12978,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12978 ⟨48,by decide⟩).lower ∧ (cell12978 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12978 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12978 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12978 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12978 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12978 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12978,cell12978,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12978 ⟨49,by decide⟩).lower ∧ (cell12978 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12978 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12978 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12978 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12978 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12978 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12978,cell12978,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12978 ⟨50,by decide⟩).lower ∧ (cell12978 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12978 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12978 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12978 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12978 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12978 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12978,cell12978,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12978 ⟨51,by decide⟩).lower ∧ (cell12978 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12978 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12978 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12978 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12978 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12978 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12978,cell12978,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12978 ⟨52,by decide⟩).lower ∧ (cell12978 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12978 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12978 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12978 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12978 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12978 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12978,cell12978,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12978 i).lower ∧
    (cell12978 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12978 i).upper ≤ (0.532 : ℝ) ∧
    (cell12978 i).centre ≤ (0.1 : ℝ) ∧ (cell12978 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12978 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12978 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12978

/-! The local source numeric instances at 12978 have no network premises. -/
namespace BstLean.Part269.N12978
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12978)
open BstLean.Part268 (cell12978)

noncomputable def sourceNumerics12978 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12978 (cell12978 i)
      scalarRow12978.M scalarRow12978.H scalarRow12978.xi := by
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
    energy_allowance := scalarRow12978.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12978]
    centre_nonneg := (scalarRow12978.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D25.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12978])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12978
/-! Actual 12979 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12979
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12979 ≤ (1.035418881023 : ℝ) := by
  have hr : (113.925414197184 : ℝ) ≤ √(12979 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.925414197184 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12979 12979 (11 / 1000) ≤
    (0.008390462803 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12979) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.925414197184 : ℝ) ≤ √(12979 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12979)
  have hdiv : K / √(12979 : ℝ) ≤ K / 113.925414197184 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.925414197184 ≤ (0.008390462803 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12979.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12979 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12979 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12979 := gPlus_lower 12979
end BstLean.Part269.N12979

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12979
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035418881022 : ℝ) ≤ wn 12979 := by
  have hn : √(12979 : ℝ) ≤ 113.925414197185 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12979 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.925414197185 ≤ 2 / √(12979 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000246373492 : ℝ) ≤ rhoBar 12979 BstLean.Part154.csC ∧
    rhoBar 12979 BstLean.Part154.csC ≤ 0.000246373873 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035418881022 : ℝ) / (1.295212 * 12979) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035418881023 : ℝ) / (1.29521 * 12979) := by gcongr
      _ ≤ (0.000246373873 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12979 BstLean.Part154.csC) ≤ 0.000985556193 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12979 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12979 BstLean.Part154.csC) (piBar (rhoBar 12979 BstLean.Part154.csC)) ≤ 0.000188181835 ∧
    cc1 (rhoBar 12979 BstLean.Part154.csC) (piBar (rhoBar 12979 BstLean.Part154.csC)) ≤ 0.000119741391 ∧
    cc2 (rhoBar 12979 BstLean.Part154.csC) ≤ 0.000069510842 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12979 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12979 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12979 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12979 BstLean.Part154.csC * nuR (rhoBar 12979 BstLean.Part154.csC)) ≤ 0.000492762922 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000246373873 : ℝ) * 0.000985556193 := by gcongr
      _ ≤ (0.000492762922 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12979 BstLean.Part154.csC) * nuR (rhoBar 12979 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000985556193 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12979 BstLean.Part154.csC) * rhoBar 12979 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000246373873 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000246373873 / 2 + 0.399 * 0.000985556193 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000188181835 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000492762922 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119741391 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000246373873 / 1.414213562 := by gcongr
      _ ≤ (0.000069510842 : ℝ) := by norm_num

end BstLean.Part269.N12979

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12979
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12979 BstLean.Part154.csC) (piBar (rhoBar 12979 BstLean.Part154.csC)) ≤ 1.52929E-7 := by
  have hr0 : 0 ≤ rhoBar 12979 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12979 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12979 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12979 BstLean.Part154.csC) (piBar (rhoBar 12979 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12979 BstLean.Part154.csC) (piBar (rhoBar 12979 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12979 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000188181835 : ℝ) ^ 2 + 0.000119741391 ^ 2 + 3 * 0.000069510842 ^ 2 +
        2 * 0.797885 * 0.000188181835 * 0.000119741391 + 2 * 0.000188181835 * 0.000069510842 +
        4 * 0.797885 * 0.000119741391 * 0.000069510842 := by gcongr
    _ ≤ (1.52929E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12979 BstLean.Part154.csC Θ ≤ 0.002570821606 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12979 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12979 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12979 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12979 BstLean.Part154.csC) (piBar (rhoBar 12979 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12979 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035418881023 * 1.52929E-7 / (0.000246373492 : ℝ) := by gcongr
    _ ≤ 0.002570821606 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12979 BstLean.Part154.csC Θ ≤ 0.002851396174 + 0.000649607359 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12979 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12979 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12979 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035418881023 : ℝ) * ((2 * Θ * 0.000246373873 +
        (6863 / 10000) * 0.000246373873 * 12979 * 0.000985556193) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002851396174 + 0.000649607359 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12979 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12979 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12979 0.011 Θ ∧ gammaRatio 12979 0.011 Θ ≤ 0.000084696967 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12979 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035418881023 : ℝ) * 0.525 / ((1 - 0.011) * 12979) := by gcongr
      _ ≤ (0.000084696967 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12979 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12979 0.011 Θ) :=
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
    badAllowance 12979 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000421835223 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12979 BstLean.Part154.csC) 1.22 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 2 (rhoBar 12979 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12979 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12979 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12979 0.011 Θ) 1.12 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 1 (gammaRatio 12979 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12979 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12979 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12979 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12979 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035418881023 : ℝ) * 12979 *
        (1.5230E-8 / 1.1045361 + 1.8602E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000421835223 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12979 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003273231397 + 0.003220428965 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12979

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12979
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12979 BstLean.Part154.csC) (piBar (rhoBar 12979 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12979 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12979 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12979 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12979 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12979 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12979 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12979 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12979 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12979 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12979 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12979 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12979 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12979 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12979 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051911056257 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12979) ≤ 0.010482626634 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12979 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035418881023)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010482626634 + 2 * 0.737676 / 12979) := by gcongr
    _ ≤ (0.051911056257 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12979 12 ≤ 0.0015 := by
  exact BstLean.Part269.S25.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12979

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12979
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560515914276 : ℝ) ≤ plow 12979 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12979) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052470556604)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001349681344) : eMP 12979 0.011 xi bn ≤ 0.001162322917 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12979 : ℝ) * (1 - 0.011))) ≤ 0.000574740526 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001349681344 / (12979 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000574740526 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000574740526 : ℝ) + 3.141593 * 0.052470556604 / (12979 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001162322917 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052470556604)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001349681344) : PiBarMP 12979 12 0.011 xi bn ≤ 0.159491150927 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12979 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036738009527 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.297091754378 : ℝ) ≤ √((12979 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.925414197184 : ℝ) ≤ √(12979 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12979) ≤ 0.122294119894 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036738009527 + 0.052470556604 * 1.772454 / (2 * (113.297091754378 : ℝ))) * (1 + 0.001162322917) +
        8 / (12979 * 113.925414197184) + 0.122294119894 := by gcongr
    _ ≤ (0.159491150927 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052470556604)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001349681344) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280975581237) :
    parallelOracle 12979 0.011 xi bn cd ≤ 0.160460194111 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12979 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12979 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560515914276 : ℝ) ≤ plow 12979 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.925414197184 : ℝ) ≤ √(12979 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280975581237 : ℝ) / (2 * 0.560515914276 * 113.925414197184)) * 0.159491150927 +
        0.280975581237 ^ 2 / (2 * 0.560515914276 * 113.925414197184) := by gcongr
    _ ≤ (0.160460194111 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052470556604) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001349681344)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280975581237) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12979 12979 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560515914276 : ℝ) ≤ plow 12979 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.925414197184 : ℝ) ≤ √(12979 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12979 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12979 Θ 1.22 ≤ 0.011640076180 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.925414197184 := by gcongr <;> linarith
      _ ≤ (0.011640076180 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12979 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12979 12979 0.011 ≤ 0.008390462803 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12979 12979 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12979 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12979 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12979 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12979 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160460194111 + 0.011640076180 + (0.008390462803 : ℝ) *
        (1 + 2 * (0.280975581237 + 0.011640076180) / (0.560515914276 * 113.925414197184))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12979]

end BstLean.Part269.N12979

/-! The original eight local profiles supply actual 12979 moment certificates. -/
namespace BstLean.Part269.N12979
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12979 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12979 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12979 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052470556604 ∧
    0 ≤ bN 12979 BstLean.Part154.csC (groupTheta g) ∧ bN 12979 BstLean.Part154.csC (groupTheta g) ≤ 0.001349681344 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12979 12979 0.011
      (momentAllowance 12979 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12979 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12979 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12979 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12979 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12979 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229064524980 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12979 0.011
      (momentAllowance 12979 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12979 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12979
/-! The actual computed-centre upper energy formula at 12979. -/
namespace BstLean.Part269.N12979
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12979

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12979
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12979)
open BstLean.Part268 (cell12979)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084715284980
  | 2 => 0.085644690451
  | 3 => 0.086570416936
  | 4 => 0.087493454951
  | 5 => 0.088415015206
  | 6 => 0.089336562875
  | 7 => 0.090259855397
  | 8 => 0.091186983898
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12979 12979 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12979 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003274156000 + 0.003221457154 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S25.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12979

/-! Actual upper energy certificates on all 43 source endpoints at 12979. -/
namespace BstLean.Part269.N12979
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12979)
open BstLean.Part268 (cell12979)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12979 (gMinus 12979) (1 - (cell12979 i).lower) ≤ 1 ∧
    energyUpper 12979 (gMinus 12979) (BstLean.Part211.gPlus 12979)
      (finiteEnergy 12979 12979 0.011) (1 - (cell12979 i).lower) ≤
      (cell12979 i).energy := by
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
      have E := BstLean.Part269.S25.uniformEnergy10 (n := 12979) (by norm_num)
        (q := 1 - (cell12979 ⟨10,by decide⟩).lower)
        (by norm_num [cell12979]) (by norm_num [cell12979])
      exact ⟨E.1,E.2.trans (by norm_num [cell12979])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy11 (n := 12979) (by norm_num)
        (q := 1 - (cell12979 ⟨11,by decide⟩).lower)
        (by norm_num [cell12979]) (by norm_num [cell12979])
      exact ⟨E.1,E.2.trans (by norm_num [cell12979])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy12 (n := 12979) (by norm_num)
        (q := 1 - (cell12979 ⟨12,by decide⟩).lower)
        (by norm_num [cell12979]) (by norm_num [cell12979])
      exact ⟨E.1,E.2.trans (by norm_num [cell12979])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy13 (n := 12979) (by norm_num)
        (q := 1 - (cell12979 ⟨13,by decide⟩).lower)
        (by norm_num [cell12979]) (by norm_num [cell12979])
      exact ⟨E.1,E.2.trans (by norm_num [cell12979])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy14 (n := 12979) (by norm_num)
        (q := 1 - (cell12979 ⟨14,by decide⟩).lower)
        (by norm_num [cell12979]) (by norm_num [cell12979])
      exact ⟨E.1,E.2.trans (by norm_num [cell12979])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy15 (n := 12979) (by norm_num)
        (q := 1 - (cell12979 ⟨15,by decide⟩).lower)
        (by norm_num [cell12979]) (by norm_num [cell12979])
      exact ⟨E.1,E.2.trans (by norm_num [cell12979])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy16 (n := 12979) (by norm_num)
        (q := 1 - (cell12979 ⟨16,by decide⟩).lower)
        (by norm_num [cell12979]) (by norm_num [cell12979])
      exact ⟨E.1,E.2.trans (by norm_num [cell12979])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy17 (n := 12979) (by norm_num)
        (q := 1 - (cell12979 ⟨17,by decide⟩).lower)
        (by norm_num [cell12979]) (by norm_num [cell12979])
      exact ⟨E.1,E.2.trans (by norm_num [cell12979])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy18 (n := 12979) (by norm_num)
        (q := 1 - (cell12979 ⟨18,by decide⟩).lower)
        (by norm_num [cell12979]) (by norm_num [cell12979])
      exact ⟨E.1,E.2.trans (by norm_num [cell12979])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy19 (n := 12979) (by norm_num)
        (q := 1 - (cell12979 ⟨19,by decide⟩).lower)
        (by norm_num [cell12979]) (by norm_num [cell12979])
      exact ⟨E.1,E.2.trans (by norm_num [cell12979])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy20 (n := 12979) (by norm_num)
        (q := 1 - (cell12979 ⟨20,by decide⟩).lower)
        (by norm_num [cell12979]) (by norm_num [cell12979])
      exact ⟨E.1,E.2.trans (by norm_num [cell12979])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy21 (n := 12979) (by norm_num)
        (q := 1 - (cell12979 ⟨21,by decide⟩).lower)
        (by norm_num [cell12979]) (by norm_num [cell12979])
      exact ⟨E.1,E.2.trans (by norm_num [cell12979])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy22 (n := 12979) (by norm_num)
        (q := 1 - (cell12979 ⟨22,by decide⟩).lower)
        (by norm_num [cell12979]) (by norm_num [cell12979])
      exact ⟨E.1,E.2.trans (by norm_num [cell12979])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy23 (n := 12979) (by norm_num)
        (q := 1 - (cell12979 ⟨23,by decide⟩).lower)
        (by norm_num [cell12979]) (by norm_num [cell12979])
      exact ⟨E.1,E.2.trans (by norm_num [cell12979])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy24 (n := 12979) (by norm_num)
        (q := 1 - (cell12979 ⟨24,by decide⟩).lower)
        (by norm_num [cell12979]) (by norm_num [cell12979])
      exact ⟨E.1,E.2.trans (by norm_num [cell12979])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy25 (n := 12979) (by norm_num)
        (q := 1 - (cell12979 ⟨25,by decide⟩).lower)
        (by norm_num [cell12979]) (by norm_num [cell12979])
      exact ⟨E.1,E.2.trans (by norm_num [cell12979])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy26 (n := 12979) (by norm_num)
        (q := 1 - (cell12979 ⟨26,by decide⟩).lower)
        (by norm_num [cell12979]) (by norm_num [cell12979])
      exact ⟨E.1,E.2.trans (by norm_num [cell12979])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy27 (n := 12979) (by norm_num)
        (q := 1 - (cell12979 ⟨27,by decide⟩).lower)
        (by norm_num [cell12979]) (by norm_num [cell12979])
      exact ⟨E.1,E.2.trans (by norm_num [cell12979])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy28 (n := 12979) (by norm_num)
        (q := 1 - (cell12979 ⟨28,by decide⟩).lower)
        (by norm_num [cell12979]) (by norm_num [cell12979])
      exact ⟨E.1,E.2.trans (by norm_num [cell12979])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy29 (n := 12979) (by norm_num)
        (q := 1 - (cell12979 ⟨29,by decide⟩).lower)
        (by norm_num [cell12979]) (by norm_num [cell12979])
      exact ⟨E.1,E.2.trans (by norm_num [cell12979])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy30 (n := 12979) (by norm_num)
        (q := 1 - (cell12979 ⟨30,by decide⟩).lower)
        (by norm_num [cell12979]) (by norm_num [cell12979])
      exact ⟨E.1,E.2.trans (by norm_num [cell12979])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy31 (n := 12979) (by norm_num)
        (q := 1 - (cell12979 ⟨31,by decide⟩).lower)
        (by norm_num [cell12979]) (by norm_num [cell12979])
      exact ⟨E.1,E.2.trans (by norm_num [cell12979])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy32 (n := 12979) (by norm_num)
        (q := 1 - (cell12979 ⟨32,by decide⟩).lower)
        (by norm_num [cell12979]) (by norm_num [cell12979])
      exact ⟨E.1,E.2.trans (by norm_num [cell12979])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy33 (n := 12979) (by norm_num)
        (q := 1 - (cell12979 ⟨33,by decide⟩).lower)
        (by norm_num [cell12979]) (by norm_num [cell12979])
      exact ⟨E.1,E.2.trans (by norm_num [cell12979])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy34 (n := 12979) (by norm_num)
        (q := 1 - (cell12979 ⟨34,by decide⟩).lower)
        (by norm_num [cell12979]) (by norm_num [cell12979])
      exact ⟨E.1,E.2.trans (by norm_num [cell12979])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy35 (n := 12979) (by norm_num)
        (q := 1 - (cell12979 ⟨35,by decide⟩).lower)
        (by norm_num [cell12979]) (by norm_num [cell12979])
      exact ⟨E.1,E.2.trans (by norm_num [cell12979])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy36 (n := 12979) (by norm_num)
        (q := 1 - (cell12979 ⟨36,by decide⟩).lower)
        (by norm_num [cell12979]) (by norm_num [cell12979])
      exact ⟨E.1,E.2.trans (by norm_num [cell12979])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy37 (n := 12979) (by norm_num)
        (q := 1 - (cell12979 ⟨37,by decide⟩).lower)
        (by norm_num [cell12979]) (by norm_num [cell12979])
      exact ⟨E.1,E.2.trans (by norm_num [cell12979])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy38 (n := 12979) (by norm_num)
        (q := 1 - (cell12979 ⟨38,by decide⟩).lower)
        (by norm_num [cell12979]) (by norm_num [cell12979])
      exact ⟨E.1,E.2.trans (by norm_num [cell12979])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy39 (n := 12979) (by norm_num)
        (q := 1 - (cell12979 ⟨39,by decide⟩).lower)
        (by norm_num [cell12979]) (by norm_num [cell12979])
      exact ⟨E.1,E.2.trans (by norm_num [cell12979])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy40 (n := 12979) (by norm_num)
        (q := 1 - (cell12979 ⟨40,by decide⟩).lower)
        (by norm_num [cell12979]) (by norm_num [cell12979])
      exact ⟨E.1,E.2.trans (by norm_num [cell12979])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy41 (n := 12979) (by norm_num)
        (q := 1 - (cell12979 ⟨41,by decide⟩).lower)
        (by norm_num [cell12979]) (by norm_num [cell12979])
      exact ⟨E.1,E.2.trans (by norm_num [cell12979])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy42 (n := 12979) (by norm_num)
        (q := 1 - (cell12979 ⟨42,by decide⟩).lower)
        (by norm_num [cell12979]) (by norm_num [cell12979])
      exact ⟨E.1,E.2.trans (by norm_num [cell12979])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy43 (n := 12979) (by norm_num)
        (q := 1 - (cell12979 ⟨43,by decide⟩).lower)
        (by norm_num [cell12979]) (by norm_num [cell12979])
      exact ⟨E.1,E.2.trans (by norm_num [cell12979])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy44 (n := 12979) (by norm_num)
        (q := 1 - (cell12979 ⟨44,by decide⟩).lower)
        (by norm_num [cell12979]) (by norm_num [cell12979])
      exact ⟨E.1,E.2.trans (by norm_num [cell12979])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy45 (n := 12979) (by norm_num)
        (q := 1 - (cell12979 ⟨45,by decide⟩).lower)
        (by norm_num [cell12979]) (by norm_num [cell12979])
      exact ⟨E.1,E.2.trans (by norm_num [cell12979])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy46 (n := 12979) (by norm_num)
        (q := 1 - (cell12979 ⟨46,by decide⟩).lower)
        (by norm_num [cell12979]) (by norm_num [cell12979])
      exact ⟨E.1,E.2.trans (by norm_num [cell12979])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy47 (n := 12979) (by norm_num)
        (q := 1 - (cell12979 ⟨47,by decide⟩).lower)
        (by norm_num [cell12979]) (by norm_num [cell12979])
      exact ⟨E.1,E.2.trans (by norm_num [cell12979])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy48 (n := 12979) (by norm_num)
        (q := 1 - (cell12979 ⟨48,by decide⟩).lower)
        (by norm_num [cell12979]) (by norm_num [cell12979])
      exact ⟨E.1,E.2.trans (by norm_num [cell12979])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy49 (n := 12979) (by norm_num)
        (q := 1 - (cell12979 ⟨49,by decide⟩).lower)
        (by norm_num [cell12979]) (by norm_num [cell12979])
      exact ⟨E.1,E.2.trans (by norm_num [cell12979])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy50 (n := 12979) (by norm_num)
        (q := 1 - (cell12979 ⟨50,by decide⟩).lower)
        (by norm_num [cell12979]) (by norm_num [cell12979])
      exact ⟨E.1,E.2.trans (by norm_num [cell12979])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy51 (n := 12979) (by norm_num)
        (q := 1 - (cell12979 ⟨51,by decide⟩).lower)
        (by norm_num [cell12979]) (by norm_num [cell12979])
      exact ⟨E.1,E.2.trans (by norm_num [cell12979])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy52 (n := 12979) (by norm_num)
        (q := 1 - (cell12979 ⟨52,by decide⟩).lower)
        (by norm_num [cell12979]) (by norm_num [cell12979])
      exact ⟨E.1,E.2.trans (by norm_num [cell12979])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12979

/-! Source-cell containment and simple scalar guards at 12979. -/
namespace BstLean.Part269.N12979
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12979)
open BstLean.Part268 (cell12979)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12979 ⟨10,by decide⟩).lower ∧ (cell12979 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12979 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12979 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12979 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12979 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12979 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12979,cell12979,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12979 ⟨11,by decide⟩).lower ∧ (cell12979 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12979 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12979 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12979 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12979 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12979 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12979,cell12979,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12979 ⟨12,by decide⟩).lower ∧ (cell12979 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12979 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12979 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12979 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12979 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12979 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12979,cell12979,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12979 ⟨13,by decide⟩).lower ∧ (cell12979 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12979 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12979 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12979 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12979 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12979 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12979,cell12979,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12979 ⟨14,by decide⟩).lower ∧ (cell12979 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12979 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12979 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12979 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12979 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12979 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12979,cell12979,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12979 ⟨15,by decide⟩).lower ∧ (cell12979 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12979 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12979 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12979 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12979 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12979 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12979,cell12979,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12979 ⟨16,by decide⟩).lower ∧ (cell12979 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12979 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12979 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12979 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12979 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12979 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12979,cell12979,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12979 ⟨17,by decide⟩).lower ∧ (cell12979 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12979 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12979 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12979 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12979 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12979 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12979,cell12979,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12979 ⟨18,by decide⟩).lower ∧ (cell12979 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12979 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12979 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12979 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12979 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12979 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12979,cell12979,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12979 ⟨19,by decide⟩).lower ∧ (cell12979 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12979 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12979 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12979 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12979 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12979 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12979,cell12979,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12979 ⟨20,by decide⟩).lower ∧ (cell12979 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12979 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12979 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12979 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12979 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12979 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12979,cell12979,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12979 ⟨21,by decide⟩).lower ∧ (cell12979 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12979 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12979 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12979 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12979 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12979 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12979,cell12979,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12979 ⟨22,by decide⟩).lower ∧ (cell12979 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12979 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12979 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12979 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12979 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12979 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12979,cell12979,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12979 ⟨23,by decide⟩).lower ∧ (cell12979 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12979 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12979 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12979 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12979 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12979 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12979,cell12979,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12979 ⟨24,by decide⟩).lower ∧ (cell12979 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12979 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12979 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12979 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12979 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12979 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12979,cell12979,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12979 ⟨25,by decide⟩).lower ∧ (cell12979 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12979 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12979 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12979 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12979 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12979 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12979,cell12979,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12979 ⟨26,by decide⟩).lower ∧ (cell12979 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12979 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12979 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12979 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12979 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12979 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12979,cell12979,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12979 ⟨27,by decide⟩).lower ∧ (cell12979 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12979 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12979 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12979 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12979 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12979 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12979,cell12979,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12979 ⟨28,by decide⟩).lower ∧ (cell12979 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12979 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12979 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12979 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12979 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12979 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12979,cell12979,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12979 ⟨29,by decide⟩).lower ∧ (cell12979 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12979 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12979 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12979 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12979 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12979 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12979,cell12979,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12979 ⟨30,by decide⟩).lower ∧ (cell12979 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12979 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12979 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12979 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12979 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12979 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12979,cell12979,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12979 ⟨31,by decide⟩).lower ∧ (cell12979 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12979 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12979 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12979 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12979 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12979 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12979,cell12979,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12979 ⟨32,by decide⟩).lower ∧ (cell12979 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12979 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12979 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12979 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12979 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12979 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12979,cell12979,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12979 ⟨33,by decide⟩).lower ∧ (cell12979 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12979 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12979 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12979 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12979 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12979 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12979,cell12979,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12979 ⟨34,by decide⟩).lower ∧ (cell12979 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12979 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12979 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12979 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12979 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12979 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12979,cell12979,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12979 ⟨35,by decide⟩).lower ∧ (cell12979 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12979 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12979 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12979 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12979 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12979 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12979,cell12979,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12979 ⟨36,by decide⟩).lower ∧ (cell12979 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12979 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12979 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12979 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12979 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12979 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12979,cell12979,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12979 ⟨37,by decide⟩).lower ∧ (cell12979 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12979 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12979 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12979 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12979 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12979 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12979,cell12979,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12979 ⟨38,by decide⟩).lower ∧ (cell12979 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12979 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12979 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12979 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12979 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12979 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12979,cell12979,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12979 ⟨39,by decide⟩).lower ∧ (cell12979 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12979 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12979 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12979 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12979 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12979 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12979,cell12979,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12979 ⟨40,by decide⟩).lower ∧ (cell12979 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12979 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12979 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12979 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12979 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12979 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12979,cell12979,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12979 ⟨41,by decide⟩).lower ∧ (cell12979 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12979 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12979 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12979 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12979 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12979 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12979,cell12979,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12979 ⟨42,by decide⟩).lower ∧ (cell12979 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12979 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12979 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12979 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12979 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12979 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12979,cell12979,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12979 ⟨43,by decide⟩).lower ∧ (cell12979 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12979 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12979 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12979 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12979 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12979 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12979,cell12979,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12979 ⟨44,by decide⟩).lower ∧ (cell12979 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12979 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12979 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12979 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12979 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12979 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12979,cell12979,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12979 ⟨45,by decide⟩).lower ∧ (cell12979 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12979 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12979 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12979 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12979 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12979 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12979,cell12979,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12979 ⟨46,by decide⟩).lower ∧ (cell12979 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12979 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12979 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12979 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12979 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12979 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12979,cell12979,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12979 ⟨47,by decide⟩).lower ∧ (cell12979 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12979 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12979 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12979 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12979 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12979 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12979,cell12979,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12979 ⟨48,by decide⟩).lower ∧ (cell12979 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12979 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12979 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12979 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12979 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12979 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12979,cell12979,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12979 ⟨49,by decide⟩).lower ∧ (cell12979 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12979 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12979 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12979 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12979 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12979 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12979,cell12979,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12979 ⟨50,by decide⟩).lower ∧ (cell12979 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12979 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12979 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12979 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12979 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12979 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12979,cell12979,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12979 ⟨51,by decide⟩).lower ∧ (cell12979 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12979 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12979 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12979 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12979 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12979 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12979,cell12979,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12979 ⟨52,by decide⟩).lower ∧ (cell12979 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12979 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12979 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12979 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12979 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12979 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12979,cell12979,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12979 i).lower ∧
    (cell12979 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12979 i).upper ≤ (0.532 : ℝ) ∧
    (cell12979 i).centre ≤ (0.1 : ℝ) ∧ (cell12979 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12979 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12979 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12979

/-! The local source numeric instances at 12979 have no network premises. -/
namespace BstLean.Part269.N12979
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12979)
open BstLean.Part268 (cell12979)

noncomputable def sourceNumerics12979 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12979 (cell12979 i)
      scalarRow12979.M scalarRow12979.H scalarRow12979.xi := by
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
    energy_allowance := scalarRow12979.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12979]
    centre_nonneg := (scalarRow12979.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D25.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12979])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12979
/-! Actual 12980 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12980
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12980 ≤ (1.035417504761 : ℝ) := by
  have hr : (113.929802949008 : ℝ) ≤ √(12980 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.929802949008 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12980 12980 (11 / 1000) ≤
    (0.008390139587 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12980) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.929802949008 : ℝ) ≤ √(12980 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12980)
  have hdiv : K / √(12980 : ℝ) ≤ K / 113.929802949008 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.929802949008 ≤ (0.008390139587 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12980.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12980 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12980 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12980 := gPlus_lower 12980
end BstLean.Part269.N12980

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12980
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035417504760 : ℝ) ≤ wn 12980 := by
  have hn : √(12980 : ℝ) ≤ 113.929802949009 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12980 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.929802949009 ≤ 2 / √(12980 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000246354183 : ℝ) ≤ rhoBar 12980 BstLean.Part154.csC ∧
    rhoBar 12980 BstLean.Part154.csC ≤ 0.000246354565 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035417504760 : ℝ) / (1.295212 * 12980) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035417504761 : ℝ) / (1.29521 * 12980) := by gcongr
      _ ≤ (0.000246354565 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12980 BstLean.Part154.csC) ≤ 0.000985478951 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12980 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12980 BstLean.Part154.csC) (piBar (rhoBar 12980 BstLean.Part154.csC)) ≤ 0.000188167087 ∧
    cc1 (rhoBar 12980 BstLean.Part154.csC) (piBar (rhoBar 12980 BstLean.Part154.csC)) ≤ 0.000119732006 ∧
    cc2 (rhoBar 12980 BstLean.Part154.csC) ≤ 0.000069505395 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12980 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12980 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12980 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12980 BstLean.Part154.csC * nuR (rhoBar 12980 BstLean.Part154.csC)) ≤ 0.000492724303 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000246354565 : ℝ) * 0.000985478951 := by gcongr
      _ ≤ (0.000492724303 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12980 BstLean.Part154.csC) * nuR (rhoBar 12980 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000985478951 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12980 BstLean.Part154.csC) * rhoBar 12980 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000246354565 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000246354565 / 2 + 0.399 * 0.000985478951 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000188167087 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000492724303 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119732006 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000246354565 / 1.414213562 := by gcongr
      _ ≤ (0.000069505395 : ℝ) := by norm_num

end BstLean.Part269.N12980

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12980
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12980 BstLean.Part154.csC) (piBar (rhoBar 12980 BstLean.Part154.csC)) ≤ 1.52906E-7 := by
  have hr0 : 0 ≤ rhoBar 12980 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12980 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12980 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12980 BstLean.Part154.csC) (piBar (rhoBar 12980 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12980 BstLean.Part154.csC) (piBar (rhoBar 12980 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12980 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000188167087 : ℝ) ^ 2 + 0.000119732006 ^ 2 + 3 * 0.000069505395 ^ 2 +
        2 * 0.797885 * 0.000188167087 * 0.000119732006 + 2 * 0.000188167087 * 0.000069505395 +
        4 * 0.797885 * 0.000119732006 * 0.000069505395 := by gcongr
    _ ≤ (1.52906E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12980 BstLean.Part154.csC Θ ≤ 0.002570633014 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12980 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12980 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12980 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12980 BstLean.Part154.csC) (piBar (rhoBar 12980 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12980 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035417504761 * 1.52906E-7 / (0.000246354183 : ℝ) := by gcongr
    _ ≤ 0.002570633014 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12980 BstLean.Part154.csC Θ ≤ 0.002851165125 + 0.000649555586 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12980 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12980 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12980 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035417504761 : ℝ) * ((2 * Θ * 0.000246354565 +
        (6863 / 10000) * 0.000246354565 * 12980 * 0.000985478951) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002851165125 + 0.000649555586 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12980 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12980 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12980 0.011 Θ ∧ gammaRatio 12980 0.011 Θ ≤ 0.000084690329 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12980 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035417504761 : ℝ) * 0.525 / ((1 - 0.011) * 12980) := by gcongr
      _ ≤ (0.000084690329 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12980 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12980 0.011 Θ) :=
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
    badAllowance 12980 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000421835223 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12980 BstLean.Part154.csC) 1.22 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 2 (rhoBar 12980 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12980 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12980 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12980 0.011 Θ) 1.12 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 1 (gammaRatio 12980 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12980 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12980 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12980 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12980 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035417504761 : ℝ) * 12980 *
        (1.5230E-8 / 1.1045361 + 1.8602E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000421835223 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12980 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003273000348 + 0.003220188600 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12980

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12980
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12980 BstLean.Part154.csC) (piBar (rhoBar 12980 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12980 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12980 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12980 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12980 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12980 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12980 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12980 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12980 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12980 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12980 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12980 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12980 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12980 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12980 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051909035112 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12980) ≤ 0.010482222827 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12980 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035417504761)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010482222827 + 2 * 0.737676 / 12980) := by gcongr
    _ ≤ (0.051909035112 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12980 12 ≤ 0.0015 := by
  exact BstLean.Part269.S25.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12980

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12980
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560515957573 : ℝ) ≤ plow 12980 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12980) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052470199363)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001349582333) : eMP 12980 0.011 xi bn ≤ 0.001162235398 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12980 : ℝ) * (1 - 0.011))) ≤ 0.000574697305 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001349582333 / (12980 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000574697305 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000574697305 : ℝ) + 3.141593 * 0.052470199363 / (12980 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001162235398 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052470199363)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001349582333) : PiBarMP 12980 12 0.011 xi bn ≤ 0.159485068348 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12980 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036736661975 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.301456301320 : ℝ) ≤ √((12980 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.929802949008 : ℝ) ≤ √(12980 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12980) ≤ 0.122289408936 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036736661975 + 0.052470199363 * 1.772454 / (2 * (113.301456301320 : ℝ))) * (1 + 0.001162235398) +
        8 / (12980 * 113.929802949008) + 0.122289408936 := by gcongr
    _ ≤ (0.159485068348 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052470199363)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001349582333) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280972780308) :
    parallelOracle 12980 0.011 xi bn cd ≤ 0.160454044926 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12980 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12980 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560515957573 : ℝ) ≤ plow 12980 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.929802949008 : ℝ) ≤ √(12980 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280972780308 : ℝ) / (2 * 0.560515957573 * 113.929802949008)) * 0.159485068348 +
        0.280972780308 ^ 2 / (2 * 0.560515957573 * 113.929802949008) := by gcongr
    _ ≤ (0.160454044926 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052470199363) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001349582333)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280972780308) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12980 12980 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560515957573 : ℝ) ≤ plow 12980 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.929802949008 : ℝ) ≤ √(12980 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12980 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12980 Θ 1.22 ≤ 0.011639627786 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.929802949008 := by gcongr <;> linarith
      _ ≤ (0.011639627786 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12980 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12980 12980 0.011 ≤ 0.008390139587 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12980 12980 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12980 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12980 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12980 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12980 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160454044926 + 0.011639627786 + (0.008390139587 : ℝ) *
        (1 + 2 * (0.280972780308 + 0.011639627786) / (0.560515957573 * 113.929802949008))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12980]

end BstLean.Part269.N12980

/-! The original eight local profiles supply actual 12980 moment certificates. -/
namespace BstLean.Part269.N12980
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12980 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12980 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12980 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052470199363 ∧
    0 ≤ bN 12980 BstLean.Part154.csC (groupTheta g) ∧ bN 12980 BstLean.Part154.csC (groupTheta g) ≤ 0.001349582333 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12980 12980 0.011
      (momentAllowance 12980 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12980 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12980 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12980 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12980 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12980 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229063745196 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12980 0.011
      (momentAllowance 12980 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12980 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12980
/-! The actual computed-centre upper energy formula at 12980. -/
namespace BstLean.Part269.N12980
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12980

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12980
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12980)
open BstLean.Part268 (cell12980)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084712649652
  | 2 => 0.085642019969
  | 3 => 0.086567705896
  | 4 => 0.087490696691
  | 5 => 0.088412201573
  | 6 => 0.089333683966
  | 7 => 0.090256899271
  | 8 => 0.091183936249
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12980 12980 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12980 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003274156000 + 0.003221457154 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S25.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12980

/-! Actual upper energy certificates on all 43 source endpoints at 12980. -/
namespace BstLean.Part269.N12980
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12980)
open BstLean.Part268 (cell12980)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12980 (gMinus 12980) (1 - (cell12980 i).lower) ≤ 1 ∧
    energyUpper 12980 (gMinus 12980) (BstLean.Part211.gPlus 12980)
      (finiteEnergy 12980 12980 0.011) (1 - (cell12980 i).lower) ≤
      (cell12980 i).energy := by
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
      have E := BstLean.Part269.S25.uniformEnergy10 (n := 12980) (by norm_num)
        (q := 1 - (cell12980 ⟨10,by decide⟩).lower)
        (by norm_num [cell12980]) (by norm_num [cell12980])
      exact ⟨E.1,E.2.trans (by norm_num [cell12980])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy11 (n := 12980) (by norm_num)
        (q := 1 - (cell12980 ⟨11,by decide⟩).lower)
        (by norm_num [cell12980]) (by norm_num [cell12980])
      exact ⟨E.1,E.2.trans (by norm_num [cell12980])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy12 (n := 12980) (by norm_num)
        (q := 1 - (cell12980 ⟨12,by decide⟩).lower)
        (by norm_num [cell12980]) (by norm_num [cell12980])
      exact ⟨E.1,E.2.trans (by norm_num [cell12980])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy13 (n := 12980) (by norm_num)
        (q := 1 - (cell12980 ⟨13,by decide⟩).lower)
        (by norm_num [cell12980]) (by norm_num [cell12980])
      exact ⟨E.1,E.2.trans (by norm_num [cell12980])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy14 (n := 12980) (by norm_num)
        (q := 1 - (cell12980 ⟨14,by decide⟩).lower)
        (by norm_num [cell12980]) (by norm_num [cell12980])
      exact ⟨E.1,E.2.trans (by norm_num [cell12980])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy15 (n := 12980) (by norm_num)
        (q := 1 - (cell12980 ⟨15,by decide⟩).lower)
        (by norm_num [cell12980]) (by norm_num [cell12980])
      exact ⟨E.1,E.2.trans (by norm_num [cell12980])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy16 (n := 12980) (by norm_num)
        (q := 1 - (cell12980 ⟨16,by decide⟩).lower)
        (by norm_num [cell12980]) (by norm_num [cell12980])
      exact ⟨E.1,E.2.trans (by norm_num [cell12980])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy17 (n := 12980) (by norm_num)
        (q := 1 - (cell12980 ⟨17,by decide⟩).lower)
        (by norm_num [cell12980]) (by norm_num [cell12980])
      exact ⟨E.1,E.2.trans (by norm_num [cell12980])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy18 (n := 12980) (by norm_num)
        (q := 1 - (cell12980 ⟨18,by decide⟩).lower)
        (by norm_num [cell12980]) (by norm_num [cell12980])
      exact ⟨E.1,E.2.trans (by norm_num [cell12980])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy19 (n := 12980) (by norm_num)
        (q := 1 - (cell12980 ⟨19,by decide⟩).lower)
        (by norm_num [cell12980]) (by norm_num [cell12980])
      exact ⟨E.1,E.2.trans (by norm_num [cell12980])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy20 (n := 12980) (by norm_num)
        (q := 1 - (cell12980 ⟨20,by decide⟩).lower)
        (by norm_num [cell12980]) (by norm_num [cell12980])
      exact ⟨E.1,E.2.trans (by norm_num [cell12980])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy21 (n := 12980) (by norm_num)
        (q := 1 - (cell12980 ⟨21,by decide⟩).lower)
        (by norm_num [cell12980]) (by norm_num [cell12980])
      exact ⟨E.1,E.2.trans (by norm_num [cell12980])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy22 (n := 12980) (by norm_num)
        (q := 1 - (cell12980 ⟨22,by decide⟩).lower)
        (by norm_num [cell12980]) (by norm_num [cell12980])
      exact ⟨E.1,E.2.trans (by norm_num [cell12980])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy23 (n := 12980) (by norm_num)
        (q := 1 - (cell12980 ⟨23,by decide⟩).lower)
        (by norm_num [cell12980]) (by norm_num [cell12980])
      exact ⟨E.1,E.2.trans (by norm_num [cell12980])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy24 (n := 12980) (by norm_num)
        (q := 1 - (cell12980 ⟨24,by decide⟩).lower)
        (by norm_num [cell12980]) (by norm_num [cell12980])
      exact ⟨E.1,E.2.trans (by norm_num [cell12980])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy25 (n := 12980) (by norm_num)
        (q := 1 - (cell12980 ⟨25,by decide⟩).lower)
        (by norm_num [cell12980]) (by norm_num [cell12980])
      exact ⟨E.1,E.2.trans (by norm_num [cell12980])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy26 (n := 12980) (by norm_num)
        (q := 1 - (cell12980 ⟨26,by decide⟩).lower)
        (by norm_num [cell12980]) (by norm_num [cell12980])
      exact ⟨E.1,E.2.trans (by norm_num [cell12980])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy27 (n := 12980) (by norm_num)
        (q := 1 - (cell12980 ⟨27,by decide⟩).lower)
        (by norm_num [cell12980]) (by norm_num [cell12980])
      exact ⟨E.1,E.2.trans (by norm_num [cell12980])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy28 (n := 12980) (by norm_num)
        (q := 1 - (cell12980 ⟨28,by decide⟩).lower)
        (by norm_num [cell12980]) (by norm_num [cell12980])
      exact ⟨E.1,E.2.trans (by norm_num [cell12980])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy29 (n := 12980) (by norm_num)
        (q := 1 - (cell12980 ⟨29,by decide⟩).lower)
        (by norm_num [cell12980]) (by norm_num [cell12980])
      exact ⟨E.1,E.2.trans (by norm_num [cell12980])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy30 (n := 12980) (by norm_num)
        (q := 1 - (cell12980 ⟨30,by decide⟩).lower)
        (by norm_num [cell12980]) (by norm_num [cell12980])
      exact ⟨E.1,E.2.trans (by norm_num [cell12980])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy31 (n := 12980) (by norm_num)
        (q := 1 - (cell12980 ⟨31,by decide⟩).lower)
        (by norm_num [cell12980]) (by norm_num [cell12980])
      exact ⟨E.1,E.2.trans (by norm_num [cell12980])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy32 (n := 12980) (by norm_num)
        (q := 1 - (cell12980 ⟨32,by decide⟩).lower)
        (by norm_num [cell12980]) (by norm_num [cell12980])
      exact ⟨E.1,E.2.trans (by norm_num [cell12980])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy33 (n := 12980) (by norm_num)
        (q := 1 - (cell12980 ⟨33,by decide⟩).lower)
        (by norm_num [cell12980]) (by norm_num [cell12980])
      exact ⟨E.1,E.2.trans (by norm_num [cell12980])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy34 (n := 12980) (by norm_num)
        (q := 1 - (cell12980 ⟨34,by decide⟩).lower)
        (by norm_num [cell12980]) (by norm_num [cell12980])
      exact ⟨E.1,E.2.trans (by norm_num [cell12980])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy35 (n := 12980) (by norm_num)
        (q := 1 - (cell12980 ⟨35,by decide⟩).lower)
        (by norm_num [cell12980]) (by norm_num [cell12980])
      exact ⟨E.1,E.2.trans (by norm_num [cell12980])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy36 (n := 12980) (by norm_num)
        (q := 1 - (cell12980 ⟨36,by decide⟩).lower)
        (by norm_num [cell12980]) (by norm_num [cell12980])
      exact ⟨E.1,E.2.trans (by norm_num [cell12980])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy37 (n := 12980) (by norm_num)
        (q := 1 - (cell12980 ⟨37,by decide⟩).lower)
        (by norm_num [cell12980]) (by norm_num [cell12980])
      exact ⟨E.1,E.2.trans (by norm_num [cell12980])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy38 (n := 12980) (by norm_num)
        (q := 1 - (cell12980 ⟨38,by decide⟩).lower)
        (by norm_num [cell12980]) (by norm_num [cell12980])
      exact ⟨E.1,E.2.trans (by norm_num [cell12980])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy39 (n := 12980) (by norm_num)
        (q := 1 - (cell12980 ⟨39,by decide⟩).lower)
        (by norm_num [cell12980]) (by norm_num [cell12980])
      exact ⟨E.1,E.2.trans (by norm_num [cell12980])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy40 (n := 12980) (by norm_num)
        (q := 1 - (cell12980 ⟨40,by decide⟩).lower)
        (by norm_num [cell12980]) (by norm_num [cell12980])
      exact ⟨E.1,E.2.trans (by norm_num [cell12980])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy41 (n := 12980) (by norm_num)
        (q := 1 - (cell12980 ⟨41,by decide⟩).lower)
        (by norm_num [cell12980]) (by norm_num [cell12980])
      exact ⟨E.1,E.2.trans (by norm_num [cell12980])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy42 (n := 12980) (by norm_num)
        (q := 1 - (cell12980 ⟨42,by decide⟩).lower)
        (by norm_num [cell12980]) (by norm_num [cell12980])
      exact ⟨E.1,E.2.trans (by norm_num [cell12980])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy43 (n := 12980) (by norm_num)
        (q := 1 - (cell12980 ⟨43,by decide⟩).lower)
        (by norm_num [cell12980]) (by norm_num [cell12980])
      exact ⟨E.1,E.2.trans (by norm_num [cell12980])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy44 (n := 12980) (by norm_num)
        (q := 1 - (cell12980 ⟨44,by decide⟩).lower)
        (by norm_num [cell12980]) (by norm_num [cell12980])
      exact ⟨E.1,E.2.trans (by norm_num [cell12980])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy45 (n := 12980) (by norm_num)
        (q := 1 - (cell12980 ⟨45,by decide⟩).lower)
        (by norm_num [cell12980]) (by norm_num [cell12980])
      exact ⟨E.1,E.2.trans (by norm_num [cell12980])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy46 (n := 12980) (by norm_num)
        (q := 1 - (cell12980 ⟨46,by decide⟩).lower)
        (by norm_num [cell12980]) (by norm_num [cell12980])
      exact ⟨E.1,E.2.trans (by norm_num [cell12980])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy47 (n := 12980) (by norm_num)
        (q := 1 - (cell12980 ⟨47,by decide⟩).lower)
        (by norm_num [cell12980]) (by norm_num [cell12980])
      exact ⟨E.1,E.2.trans (by norm_num [cell12980])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy48 (n := 12980) (by norm_num)
        (q := 1 - (cell12980 ⟨48,by decide⟩).lower)
        (by norm_num [cell12980]) (by norm_num [cell12980])
      exact ⟨E.1,E.2.trans (by norm_num [cell12980])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy49 (n := 12980) (by norm_num)
        (q := 1 - (cell12980 ⟨49,by decide⟩).lower)
        (by norm_num [cell12980]) (by norm_num [cell12980])
      exact ⟨E.1,E.2.trans (by norm_num [cell12980])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy50 (n := 12980) (by norm_num)
        (q := 1 - (cell12980 ⟨50,by decide⟩).lower)
        (by norm_num [cell12980]) (by norm_num [cell12980])
      exact ⟨E.1,E.2.trans (by norm_num [cell12980])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy51 (n := 12980) (by norm_num)
        (q := 1 - (cell12980 ⟨51,by decide⟩).lower)
        (by norm_num [cell12980]) (by norm_num [cell12980])
      exact ⟨E.1,E.2.trans (by norm_num [cell12980])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy52 (n := 12980) (by norm_num)
        (q := 1 - (cell12980 ⟨52,by decide⟩).lower)
        (by norm_num [cell12980]) (by norm_num [cell12980])
      exact ⟨E.1,E.2.trans (by norm_num [cell12980])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12980

/-! Source-cell containment and simple scalar guards at 12980. -/
namespace BstLean.Part269.N12980
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12980)
open BstLean.Part268 (cell12980)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12980 ⟨10,by decide⟩).lower ∧ (cell12980 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12980 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12980 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12980 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12980 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12980 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12980,cell12980,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12980 ⟨11,by decide⟩).lower ∧ (cell12980 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12980 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12980 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12980 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12980 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12980 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12980,cell12980,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12980 ⟨12,by decide⟩).lower ∧ (cell12980 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12980 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12980 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12980 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12980 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12980 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12980,cell12980,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12980 ⟨13,by decide⟩).lower ∧ (cell12980 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12980 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12980 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12980 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12980 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12980 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12980,cell12980,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12980 ⟨14,by decide⟩).lower ∧ (cell12980 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12980 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12980 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12980 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12980 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12980 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12980,cell12980,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12980 ⟨15,by decide⟩).lower ∧ (cell12980 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12980 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12980 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12980 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12980 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12980 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12980,cell12980,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12980 ⟨16,by decide⟩).lower ∧ (cell12980 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12980 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12980 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12980 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12980 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12980 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12980,cell12980,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12980 ⟨17,by decide⟩).lower ∧ (cell12980 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12980 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12980 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12980 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12980 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12980 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12980,cell12980,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12980 ⟨18,by decide⟩).lower ∧ (cell12980 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12980 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12980 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12980 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12980 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12980 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12980,cell12980,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12980 ⟨19,by decide⟩).lower ∧ (cell12980 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12980 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12980 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12980 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12980 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12980 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12980,cell12980,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12980 ⟨20,by decide⟩).lower ∧ (cell12980 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12980 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12980 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12980 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12980 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12980 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12980,cell12980,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12980 ⟨21,by decide⟩).lower ∧ (cell12980 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12980 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12980 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12980 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12980 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12980 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12980,cell12980,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12980 ⟨22,by decide⟩).lower ∧ (cell12980 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12980 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12980 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12980 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12980 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12980 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12980,cell12980,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12980 ⟨23,by decide⟩).lower ∧ (cell12980 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12980 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12980 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12980 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12980 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12980 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12980,cell12980,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12980 ⟨24,by decide⟩).lower ∧ (cell12980 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12980 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12980 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12980 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12980 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12980 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12980,cell12980,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12980 ⟨25,by decide⟩).lower ∧ (cell12980 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12980 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12980 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12980 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12980 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12980 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12980,cell12980,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12980 ⟨26,by decide⟩).lower ∧ (cell12980 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12980 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12980 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12980 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12980 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12980 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12980,cell12980,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12980 ⟨27,by decide⟩).lower ∧ (cell12980 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12980 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12980 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12980 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12980 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12980 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12980,cell12980,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12980 ⟨28,by decide⟩).lower ∧ (cell12980 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12980 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12980 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12980 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12980 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12980 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12980,cell12980,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12980 ⟨29,by decide⟩).lower ∧ (cell12980 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12980 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12980 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12980 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12980 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12980 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12980,cell12980,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12980 ⟨30,by decide⟩).lower ∧ (cell12980 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12980 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12980 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12980 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12980 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12980 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12980,cell12980,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12980 ⟨31,by decide⟩).lower ∧ (cell12980 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12980 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12980 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12980 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12980 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12980 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12980,cell12980,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12980 ⟨32,by decide⟩).lower ∧ (cell12980 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12980 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12980 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12980 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12980 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12980 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12980,cell12980,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12980 ⟨33,by decide⟩).lower ∧ (cell12980 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12980 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12980 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12980 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12980 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12980 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12980,cell12980,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12980 ⟨34,by decide⟩).lower ∧ (cell12980 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12980 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12980 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12980 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12980 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12980 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12980,cell12980,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12980 ⟨35,by decide⟩).lower ∧ (cell12980 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12980 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12980 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12980 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12980 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12980 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12980,cell12980,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12980 ⟨36,by decide⟩).lower ∧ (cell12980 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12980 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12980 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12980 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12980 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12980 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12980,cell12980,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12980 ⟨37,by decide⟩).lower ∧ (cell12980 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12980 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12980 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12980 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12980 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12980 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12980,cell12980,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12980 ⟨38,by decide⟩).lower ∧ (cell12980 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12980 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12980 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12980 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12980 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12980 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12980,cell12980,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12980 ⟨39,by decide⟩).lower ∧ (cell12980 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12980 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12980 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12980 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12980 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12980 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12980,cell12980,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12980 ⟨40,by decide⟩).lower ∧ (cell12980 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12980 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12980 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12980 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12980 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12980 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12980,cell12980,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12980 ⟨41,by decide⟩).lower ∧ (cell12980 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12980 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12980 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12980 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12980 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12980 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12980,cell12980,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12980 ⟨42,by decide⟩).lower ∧ (cell12980 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12980 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12980 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12980 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12980 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12980 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12980,cell12980,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12980 ⟨43,by decide⟩).lower ∧ (cell12980 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12980 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12980 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12980 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12980 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12980 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12980,cell12980,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12980 ⟨44,by decide⟩).lower ∧ (cell12980 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12980 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12980 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12980 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12980 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12980 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12980,cell12980,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12980 ⟨45,by decide⟩).lower ∧ (cell12980 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12980 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12980 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12980 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12980 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12980 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12980,cell12980,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12980 ⟨46,by decide⟩).lower ∧ (cell12980 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12980 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12980 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12980 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12980 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12980 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12980,cell12980,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12980 ⟨47,by decide⟩).lower ∧ (cell12980 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12980 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12980 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12980 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12980 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12980 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12980,cell12980,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12980 ⟨48,by decide⟩).lower ∧ (cell12980 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12980 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12980 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12980 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12980 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12980 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12980,cell12980,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12980 ⟨49,by decide⟩).lower ∧ (cell12980 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12980 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12980 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12980 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12980 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12980 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12980,cell12980,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12980 ⟨50,by decide⟩).lower ∧ (cell12980 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12980 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12980 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12980 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12980 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12980 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12980,cell12980,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12980 ⟨51,by decide⟩).lower ∧ (cell12980 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12980 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12980 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12980 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12980 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12980 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12980,cell12980,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12980 ⟨52,by decide⟩).lower ∧ (cell12980 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12980 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12980 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12980 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12980 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12980 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12980,cell12980,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12980 i).lower ∧
    (cell12980 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12980 i).upper ≤ (0.532 : ℝ) ∧
    (cell12980 i).centre ≤ (0.1 : ℝ) ∧ (cell12980 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12980 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12980 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12980

/-! The local source numeric instances at 12980 have no network premises. -/
namespace BstLean.Part269.N12980
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12980)
open BstLean.Part268 (cell12980)

noncomputable def sourceNumerics12980 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12980 (cell12980 i)
      scalarRow12980.M scalarRow12980.H scalarRow12980.xi := by
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
    energy_allowance := scalarRow12980.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12980]
    centre_nonneg := (scalarRow12980.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D25.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12980])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12980
/-! Actual 12981 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12981
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12981 ≤ (1.035416128660 : ℝ) := by
  have hr : (113.934191531778 : ℝ) ≤ √(12981 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.934191531778 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12981 12981 (11 / 1000) ≤
    (0.008389816408 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12981) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.934191531778 : ℝ) ≤ √(12981 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12981)
  have hdiv : K / √(12981 : ℝ) ≤ K / 113.934191531778 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.934191531778 ≤ (0.008389816408 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12981.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12981 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12981 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12981 := gPlus_lower 12981
end BstLean.Part269.N12981

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12981
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035416128659 : ℝ) ≤ wn 12981 := by
  have hn : √(12981 : ℝ) ≤ 113.934191531779 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12981 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.934191531779 ≤ 2 / √(12981 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000246334878 : ℝ) ≤ rhoBar 12981 BstLean.Part154.csC ∧
    rhoBar 12981 BstLean.Part154.csC ≤ 0.000246335259 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035416128659 : ℝ) / (1.295212 * 12981) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035416128660 : ℝ) / (1.29521 * 12981) := by gcongr
      _ ≤ (0.000246335259 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12981 BstLean.Part154.csC) ≤ 0.000985401718 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12981 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12981 BstLean.Part154.csC) (piBar (rhoBar 12981 BstLean.Part154.csC)) ≤ 0.000188152340 ∧
    cc1 (rhoBar 12981 BstLean.Part154.csC) (piBar (rhoBar 12981 BstLean.Part154.csC)) ≤ 0.000119722623 ∧
    cc2 (rhoBar 12981 BstLean.Part154.csC) ≤ 0.000069499948 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12981 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12981 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12981 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12981 BstLean.Part154.csC * nuR (rhoBar 12981 BstLean.Part154.csC)) ≤ 0.000492685689 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000246335259 : ℝ) * 0.000985401718 := by gcongr
      _ ≤ (0.000492685689 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12981 BstLean.Part154.csC) * nuR (rhoBar 12981 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000985401718 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12981 BstLean.Part154.csC) * rhoBar 12981 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000246335259 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000246335259 / 2 + 0.399 * 0.000985401718 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000188152340 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000492685689 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119722623 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000246335259 / 1.414213562 := by gcongr
      _ ≤ (0.000069499948 : ℝ) := by norm_num

end BstLean.Part269.N12981

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12981
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12981 BstLean.Part154.csC) (piBar (rhoBar 12981 BstLean.Part154.csC)) ≤ 1.52882E-7 := by
  have hr0 : 0 ≤ rhoBar 12981 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12981 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12981 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12981 BstLean.Part154.csC) (piBar (rhoBar 12981 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12981 BstLean.Part154.csC) (piBar (rhoBar 12981 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12981 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000188152340 : ℝ) ^ 2 + 0.000119722623 ^ 2 + 3 * 0.000069499948 ^ 2 +
        2 * 0.797885 * 0.000188152340 * 0.000119722623 + 2 * 0.000188152340 * 0.000069499948 +
        4 * 0.797885 * 0.000119722623 * 0.000069499948 := by gcongr
    _ ≤ (1.52882E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12981 BstLean.Part154.csC Θ ≤ 0.002570427540 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12981 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12981 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12981 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12981 BstLean.Part154.csC) (piBar (rhoBar 12981 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12981 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035416128660 * 1.52882E-7 / (0.000246334878 : ℝ) := by gcongr
    _ ≤ 0.002570427540 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12981 BstLean.Part154.csC Θ ≤ 0.002850934092 + 0.000649503820 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12981 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12981 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12981 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035416128660 : ℝ) * ((2 * Θ * 0.000246335259 +
        (6863 / 10000) * 0.000246335259 * 12981 * 0.000985401718) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002850934092 + 0.000649503820 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12981 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12981 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12981 0.011 Θ ∧ gammaRatio 12981 0.011 Θ ≤ 0.000084683692 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12981 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035416128660 : ℝ) * 0.525 / ((1 - 0.011) * 12981) := by gcongr
      _ ≤ (0.000084683692 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12981 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12981 0.011 Θ) :=
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
    badAllowance 12981 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000421835223 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12981 BstLean.Part154.csC) 1.22 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 2 (rhoBar 12981 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12981 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12981 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12981 0.011 Θ) 1.12 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 1 (gammaRatio 12981 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12981 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12981 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12981 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12981 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035416128660 : ℝ) * 12981 *
        (1.5230E-8 / 1.1045361 + 1.8602E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000421835223 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12981 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003272769315 + 0.003219931360 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12981

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12981
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12981 BstLean.Part154.csC) (piBar (rhoBar 12981 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12981 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12981 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12981 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12981 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12981 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12981 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12981 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12981 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12981 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12981 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12981 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12981 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12981 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12981 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051907014199 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12981) ≤ 0.010481819066 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12981 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035416128660)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010481819066 + 2 * 0.737676 / 12981) := by gcongr
    _ ≤ (0.051907014199 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12981 12 ≤ 0.0015 := by
  exact BstLean.Part269.S25.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12981

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12981
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560516000862 : ℝ) ≤ plow 12981 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12981) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052469833279)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001349474459) : eMP 12981 0.011 xi bn ≤ 0.001162144111 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12981 : ℝ) * (1 - 0.011))) ≤ 0.000574652201 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001349474459 / (12981 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000574652201 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000574652201 : ℝ) + 3.141593 * 0.052469833279 / (12981 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001162144111 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052469833279)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001349474459) : PiBarMP 12981 12 0.011 xi bn ≤ 0.159478865282 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12981 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036735193739 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.305820680139 : ℝ) ≤ √((12981 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.934191531778 : ℝ) ≤ √(12981 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12981) ≤ 0.122284698522 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036735193739 + 0.052469833279 * 1.772454 / (2 * (113.305820680139 : ℝ))) * (1 + 0.001162144111) +
        8 / (12981 * 113.934191531778) + 0.122284698522 := by gcongr
    _ ≤ (0.159478865282 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052469833279)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001349474459) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280969960306) :
    parallelOracle 12981 0.011 xi bn cd ≤ 0.160447774887 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12981 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12981 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560516000862 : ℝ) ≤ plow 12981 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.934191531778 : ℝ) ≤ √(12981 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280969960306 : ℝ) / (2 * 0.560516000862 * 113.934191531778)) * 0.159478865282 +
        0.280969960306 ^ 2 / (2 * 0.560516000862 * 113.934191531778) := by gcongr
    _ ≤ (0.160447774887 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052469833279) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001349474459)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280969960306) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12981 12981 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560516000862 : ℝ) ≤ plow 12981 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.934191531778 : ℝ) ≤ √(12981 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12981 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12981 Θ 1.22 ≤ 0.011639179444 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.934191531778 := by gcongr <;> linarith
      _ ≤ (0.011639179444 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12981 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12981 12981 0.011 ≤ 0.008389816408 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12981 12981 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12981 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12981 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12981 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12981 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160447774887 + 0.011639179444 + (0.008389816408 : ℝ) *
        (1 + 2 * (0.280969960306 + 0.011639179444) / (0.560516000862 * 113.934191531778))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12981]

end BstLean.Part269.N12981

/-! The original eight local profiles supply actual 12981 moment certificates. -/
namespace BstLean.Part269.N12981
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12981 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12981 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12981 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052469833279 ∧
    0 ≤ bN 12981 BstLean.Part154.csC (groupTheta g) ∧ bN 12981 BstLean.Part154.csC (groupTheta g) ≤ 0.001349474459 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12981 12981 0.011
      (momentAllowance 12981 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12981 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12981 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12981 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12981 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12981 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229062946107 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12981 0.011
      (momentAllowance 12981 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12981 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12981
/-! The actual computed-centre upper energy formula at 12981. -/
namespace BstLean.Part269.N12981
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12981

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12981
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12981)
open BstLean.Part268 (cell12981)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084710015147
  | 2 => 0.085639350338
  | 3 => 0.086564995745
  | 4 => 0.087487939365
  | 5 => 0.088409388928
  | 6 => 0.089330806113
  | 7 => 0.090253944282
  | 8 => 0.091180889834
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12981 12981 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12981 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003274156000 + 0.003221457154 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S25.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12981

/-! Actual upper energy certificates on all 43 source endpoints at 12981. -/
namespace BstLean.Part269.N12981
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12981)
open BstLean.Part268 (cell12981)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12981 (gMinus 12981) (1 - (cell12981 i).lower) ≤ 1 ∧
    energyUpper 12981 (gMinus 12981) (BstLean.Part211.gPlus 12981)
      (finiteEnergy 12981 12981 0.011) (1 - (cell12981 i).lower) ≤
      (cell12981 i).energy := by
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
      have E := BstLean.Part269.S25.uniformEnergy10 (n := 12981) (by norm_num)
        (q := 1 - (cell12981 ⟨10,by decide⟩).lower)
        (by norm_num [cell12981]) (by norm_num [cell12981])
      exact ⟨E.1,E.2.trans (by norm_num [cell12981])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy11 (n := 12981) (by norm_num)
        (q := 1 - (cell12981 ⟨11,by decide⟩).lower)
        (by norm_num [cell12981]) (by norm_num [cell12981])
      exact ⟨E.1,E.2.trans (by norm_num [cell12981])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy12 (n := 12981) (by norm_num)
        (q := 1 - (cell12981 ⟨12,by decide⟩).lower)
        (by norm_num [cell12981]) (by norm_num [cell12981])
      exact ⟨E.1,E.2.trans (by norm_num [cell12981])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy13 (n := 12981) (by norm_num)
        (q := 1 - (cell12981 ⟨13,by decide⟩).lower)
        (by norm_num [cell12981]) (by norm_num [cell12981])
      exact ⟨E.1,E.2.trans (by norm_num [cell12981])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy14 (n := 12981) (by norm_num)
        (q := 1 - (cell12981 ⟨14,by decide⟩).lower)
        (by norm_num [cell12981]) (by norm_num [cell12981])
      exact ⟨E.1,E.2.trans (by norm_num [cell12981])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy15 (n := 12981) (by norm_num)
        (q := 1 - (cell12981 ⟨15,by decide⟩).lower)
        (by norm_num [cell12981]) (by norm_num [cell12981])
      exact ⟨E.1,E.2.trans (by norm_num [cell12981])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy16 (n := 12981) (by norm_num)
        (q := 1 - (cell12981 ⟨16,by decide⟩).lower)
        (by norm_num [cell12981]) (by norm_num [cell12981])
      exact ⟨E.1,E.2.trans (by norm_num [cell12981])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy17 (n := 12981) (by norm_num)
        (q := 1 - (cell12981 ⟨17,by decide⟩).lower)
        (by norm_num [cell12981]) (by norm_num [cell12981])
      exact ⟨E.1,E.2.trans (by norm_num [cell12981])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy18 (n := 12981) (by norm_num)
        (q := 1 - (cell12981 ⟨18,by decide⟩).lower)
        (by norm_num [cell12981]) (by norm_num [cell12981])
      exact ⟨E.1,E.2.trans (by norm_num [cell12981])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy19 (n := 12981) (by norm_num)
        (q := 1 - (cell12981 ⟨19,by decide⟩).lower)
        (by norm_num [cell12981]) (by norm_num [cell12981])
      exact ⟨E.1,E.2.trans (by norm_num [cell12981])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy20 (n := 12981) (by norm_num)
        (q := 1 - (cell12981 ⟨20,by decide⟩).lower)
        (by norm_num [cell12981]) (by norm_num [cell12981])
      exact ⟨E.1,E.2.trans (by norm_num [cell12981])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy21 (n := 12981) (by norm_num)
        (q := 1 - (cell12981 ⟨21,by decide⟩).lower)
        (by norm_num [cell12981]) (by norm_num [cell12981])
      exact ⟨E.1,E.2.trans (by norm_num [cell12981])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy22 (n := 12981) (by norm_num)
        (q := 1 - (cell12981 ⟨22,by decide⟩).lower)
        (by norm_num [cell12981]) (by norm_num [cell12981])
      exact ⟨E.1,E.2.trans (by norm_num [cell12981])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy23 (n := 12981) (by norm_num)
        (q := 1 - (cell12981 ⟨23,by decide⟩).lower)
        (by norm_num [cell12981]) (by norm_num [cell12981])
      exact ⟨E.1,E.2.trans (by norm_num [cell12981])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy24 (n := 12981) (by norm_num)
        (q := 1 - (cell12981 ⟨24,by decide⟩).lower)
        (by norm_num [cell12981]) (by norm_num [cell12981])
      exact ⟨E.1,E.2.trans (by norm_num [cell12981])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy25 (n := 12981) (by norm_num)
        (q := 1 - (cell12981 ⟨25,by decide⟩).lower)
        (by norm_num [cell12981]) (by norm_num [cell12981])
      exact ⟨E.1,E.2.trans (by norm_num [cell12981])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy26 (n := 12981) (by norm_num)
        (q := 1 - (cell12981 ⟨26,by decide⟩).lower)
        (by norm_num [cell12981]) (by norm_num [cell12981])
      exact ⟨E.1,E.2.trans (by norm_num [cell12981])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy27 (n := 12981) (by norm_num)
        (q := 1 - (cell12981 ⟨27,by decide⟩).lower)
        (by norm_num [cell12981]) (by norm_num [cell12981])
      exact ⟨E.1,E.2.trans (by norm_num [cell12981])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy28 (n := 12981) (by norm_num)
        (q := 1 - (cell12981 ⟨28,by decide⟩).lower)
        (by norm_num [cell12981]) (by norm_num [cell12981])
      exact ⟨E.1,E.2.trans (by norm_num [cell12981])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy29 (n := 12981) (by norm_num)
        (q := 1 - (cell12981 ⟨29,by decide⟩).lower)
        (by norm_num [cell12981]) (by norm_num [cell12981])
      exact ⟨E.1,E.2.trans (by norm_num [cell12981])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy30 (n := 12981) (by norm_num)
        (q := 1 - (cell12981 ⟨30,by decide⟩).lower)
        (by norm_num [cell12981]) (by norm_num [cell12981])
      exact ⟨E.1,E.2.trans (by norm_num [cell12981])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy31 (n := 12981) (by norm_num)
        (q := 1 - (cell12981 ⟨31,by decide⟩).lower)
        (by norm_num [cell12981]) (by norm_num [cell12981])
      exact ⟨E.1,E.2.trans (by norm_num [cell12981])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy32 (n := 12981) (by norm_num)
        (q := 1 - (cell12981 ⟨32,by decide⟩).lower)
        (by norm_num [cell12981]) (by norm_num [cell12981])
      exact ⟨E.1,E.2.trans (by norm_num [cell12981])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy33 (n := 12981) (by norm_num)
        (q := 1 - (cell12981 ⟨33,by decide⟩).lower)
        (by norm_num [cell12981]) (by norm_num [cell12981])
      exact ⟨E.1,E.2.trans (by norm_num [cell12981])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy34 (n := 12981) (by norm_num)
        (q := 1 - (cell12981 ⟨34,by decide⟩).lower)
        (by norm_num [cell12981]) (by norm_num [cell12981])
      exact ⟨E.1,E.2.trans (by norm_num [cell12981])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy35 (n := 12981) (by norm_num)
        (q := 1 - (cell12981 ⟨35,by decide⟩).lower)
        (by norm_num [cell12981]) (by norm_num [cell12981])
      exact ⟨E.1,E.2.trans (by norm_num [cell12981])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy36 (n := 12981) (by norm_num)
        (q := 1 - (cell12981 ⟨36,by decide⟩).lower)
        (by norm_num [cell12981]) (by norm_num [cell12981])
      exact ⟨E.1,E.2.trans (by norm_num [cell12981])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy37 (n := 12981) (by norm_num)
        (q := 1 - (cell12981 ⟨37,by decide⟩).lower)
        (by norm_num [cell12981]) (by norm_num [cell12981])
      exact ⟨E.1,E.2.trans (by norm_num [cell12981])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy38 (n := 12981) (by norm_num)
        (q := 1 - (cell12981 ⟨38,by decide⟩).lower)
        (by norm_num [cell12981]) (by norm_num [cell12981])
      exact ⟨E.1,E.2.trans (by norm_num [cell12981])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy39 (n := 12981) (by norm_num)
        (q := 1 - (cell12981 ⟨39,by decide⟩).lower)
        (by norm_num [cell12981]) (by norm_num [cell12981])
      exact ⟨E.1,E.2.trans (by norm_num [cell12981])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy40 (n := 12981) (by norm_num)
        (q := 1 - (cell12981 ⟨40,by decide⟩).lower)
        (by norm_num [cell12981]) (by norm_num [cell12981])
      exact ⟨E.1,E.2.trans (by norm_num [cell12981])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy41 (n := 12981) (by norm_num)
        (q := 1 - (cell12981 ⟨41,by decide⟩).lower)
        (by norm_num [cell12981]) (by norm_num [cell12981])
      exact ⟨E.1,E.2.trans (by norm_num [cell12981])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy42 (n := 12981) (by norm_num)
        (q := 1 - (cell12981 ⟨42,by decide⟩).lower)
        (by norm_num [cell12981]) (by norm_num [cell12981])
      exact ⟨E.1,E.2.trans (by norm_num [cell12981])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy43 (n := 12981) (by norm_num)
        (q := 1 - (cell12981 ⟨43,by decide⟩).lower)
        (by norm_num [cell12981]) (by norm_num [cell12981])
      exact ⟨E.1,E.2.trans (by norm_num [cell12981])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy44 (n := 12981) (by norm_num)
        (q := 1 - (cell12981 ⟨44,by decide⟩).lower)
        (by norm_num [cell12981]) (by norm_num [cell12981])
      exact ⟨E.1,E.2.trans (by norm_num [cell12981])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy45 (n := 12981) (by norm_num)
        (q := 1 - (cell12981 ⟨45,by decide⟩).lower)
        (by norm_num [cell12981]) (by norm_num [cell12981])
      exact ⟨E.1,E.2.trans (by norm_num [cell12981])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy46 (n := 12981) (by norm_num)
        (q := 1 - (cell12981 ⟨46,by decide⟩).lower)
        (by norm_num [cell12981]) (by norm_num [cell12981])
      exact ⟨E.1,E.2.trans (by norm_num [cell12981])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy47 (n := 12981) (by norm_num)
        (q := 1 - (cell12981 ⟨47,by decide⟩).lower)
        (by norm_num [cell12981]) (by norm_num [cell12981])
      exact ⟨E.1,E.2.trans (by norm_num [cell12981])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy48 (n := 12981) (by norm_num)
        (q := 1 - (cell12981 ⟨48,by decide⟩).lower)
        (by norm_num [cell12981]) (by norm_num [cell12981])
      exact ⟨E.1,E.2.trans (by norm_num [cell12981])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy49 (n := 12981) (by norm_num)
        (q := 1 - (cell12981 ⟨49,by decide⟩).lower)
        (by norm_num [cell12981]) (by norm_num [cell12981])
      exact ⟨E.1,E.2.trans (by norm_num [cell12981])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy50 (n := 12981) (by norm_num)
        (q := 1 - (cell12981 ⟨50,by decide⟩).lower)
        (by norm_num [cell12981]) (by norm_num [cell12981])
      exact ⟨E.1,E.2.trans (by norm_num [cell12981])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy51 (n := 12981) (by norm_num)
        (q := 1 - (cell12981 ⟨51,by decide⟩).lower)
        (by norm_num [cell12981]) (by norm_num [cell12981])
      exact ⟨E.1,E.2.trans (by norm_num [cell12981])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy52 (n := 12981) (by norm_num)
        (q := 1 - (cell12981 ⟨52,by decide⟩).lower)
        (by norm_num [cell12981]) (by norm_num [cell12981])
      exact ⟨E.1,E.2.trans (by norm_num [cell12981])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12981

/-! Source-cell containment and simple scalar guards at 12981. -/
namespace BstLean.Part269.N12981
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12981)
open BstLean.Part268 (cell12981)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12981 ⟨10,by decide⟩).lower ∧ (cell12981 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12981 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12981 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12981 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12981 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12981 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12981,cell12981,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12981 ⟨11,by decide⟩).lower ∧ (cell12981 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12981 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12981 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12981 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12981 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12981 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12981,cell12981,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12981 ⟨12,by decide⟩).lower ∧ (cell12981 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12981 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12981 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12981 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12981 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12981 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12981,cell12981,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12981 ⟨13,by decide⟩).lower ∧ (cell12981 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12981 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12981 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12981 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12981 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12981 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12981,cell12981,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12981 ⟨14,by decide⟩).lower ∧ (cell12981 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12981 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12981 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12981 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12981 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12981 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12981,cell12981,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12981 ⟨15,by decide⟩).lower ∧ (cell12981 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12981 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12981 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12981 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12981 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12981 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12981,cell12981,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12981 ⟨16,by decide⟩).lower ∧ (cell12981 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12981 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12981 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12981 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12981 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12981 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12981,cell12981,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12981 ⟨17,by decide⟩).lower ∧ (cell12981 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12981 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12981 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12981 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12981 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12981 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12981,cell12981,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12981 ⟨18,by decide⟩).lower ∧ (cell12981 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12981 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12981 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12981 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12981 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12981 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12981,cell12981,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12981 ⟨19,by decide⟩).lower ∧ (cell12981 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12981 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12981 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12981 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12981 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12981 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12981,cell12981,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12981 ⟨20,by decide⟩).lower ∧ (cell12981 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12981 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12981 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12981 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12981 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12981 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12981,cell12981,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12981 ⟨21,by decide⟩).lower ∧ (cell12981 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12981 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12981 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12981 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12981 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12981 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12981,cell12981,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12981 ⟨22,by decide⟩).lower ∧ (cell12981 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12981 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12981 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12981 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12981 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12981 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12981,cell12981,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12981 ⟨23,by decide⟩).lower ∧ (cell12981 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12981 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12981 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12981 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12981 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12981 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12981,cell12981,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12981 ⟨24,by decide⟩).lower ∧ (cell12981 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12981 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12981 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12981 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12981 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12981 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12981,cell12981,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12981 ⟨25,by decide⟩).lower ∧ (cell12981 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12981 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12981 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12981 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12981 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12981 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12981,cell12981,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12981 ⟨26,by decide⟩).lower ∧ (cell12981 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12981 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12981 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12981 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12981 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12981 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12981,cell12981,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12981 ⟨27,by decide⟩).lower ∧ (cell12981 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12981 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12981 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12981 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12981 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12981 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12981,cell12981,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12981 ⟨28,by decide⟩).lower ∧ (cell12981 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12981 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12981 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12981 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12981 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12981 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12981,cell12981,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12981 ⟨29,by decide⟩).lower ∧ (cell12981 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12981 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12981 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12981 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12981 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12981 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12981,cell12981,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12981 ⟨30,by decide⟩).lower ∧ (cell12981 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12981 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12981 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12981 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12981 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12981 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12981,cell12981,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12981 ⟨31,by decide⟩).lower ∧ (cell12981 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12981 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12981 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12981 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12981 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12981 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12981,cell12981,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12981 ⟨32,by decide⟩).lower ∧ (cell12981 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12981 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12981 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12981 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12981 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12981 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12981,cell12981,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12981 ⟨33,by decide⟩).lower ∧ (cell12981 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12981 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12981 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12981 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12981 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12981 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12981,cell12981,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12981 ⟨34,by decide⟩).lower ∧ (cell12981 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12981 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12981 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12981 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12981 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12981 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12981,cell12981,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12981 ⟨35,by decide⟩).lower ∧ (cell12981 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12981 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12981 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12981 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12981 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12981 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12981,cell12981,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12981 ⟨36,by decide⟩).lower ∧ (cell12981 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12981 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12981 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12981 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12981 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12981 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12981,cell12981,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12981 ⟨37,by decide⟩).lower ∧ (cell12981 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12981 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12981 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12981 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12981 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12981 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12981,cell12981,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12981 ⟨38,by decide⟩).lower ∧ (cell12981 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12981 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12981 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12981 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12981 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12981 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12981,cell12981,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12981 ⟨39,by decide⟩).lower ∧ (cell12981 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12981 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12981 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12981 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12981 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12981 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12981,cell12981,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12981 ⟨40,by decide⟩).lower ∧ (cell12981 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12981 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12981 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12981 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12981 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12981 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12981,cell12981,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12981 ⟨41,by decide⟩).lower ∧ (cell12981 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12981 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12981 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12981 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12981 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12981 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12981,cell12981,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12981 ⟨42,by decide⟩).lower ∧ (cell12981 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12981 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12981 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12981 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12981 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12981 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12981,cell12981,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12981 ⟨43,by decide⟩).lower ∧ (cell12981 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12981 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12981 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12981 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12981 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12981 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12981,cell12981,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12981 ⟨44,by decide⟩).lower ∧ (cell12981 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12981 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12981 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12981 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12981 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12981 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12981,cell12981,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12981 ⟨45,by decide⟩).lower ∧ (cell12981 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12981 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12981 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12981 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12981 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12981 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12981,cell12981,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12981 ⟨46,by decide⟩).lower ∧ (cell12981 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12981 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12981 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12981 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12981 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12981 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12981,cell12981,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12981 ⟨47,by decide⟩).lower ∧ (cell12981 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12981 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12981 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12981 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12981 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12981 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12981,cell12981,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12981 ⟨48,by decide⟩).lower ∧ (cell12981 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12981 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12981 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12981 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12981 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12981 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12981,cell12981,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12981 ⟨49,by decide⟩).lower ∧ (cell12981 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12981 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12981 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12981 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12981 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12981 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12981,cell12981,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12981 ⟨50,by decide⟩).lower ∧ (cell12981 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12981 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12981 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12981 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12981 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12981 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12981,cell12981,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12981 ⟨51,by decide⟩).lower ∧ (cell12981 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12981 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12981 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12981 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12981 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12981 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12981,cell12981,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12981 ⟨52,by decide⟩).lower ∧ (cell12981 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12981 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12981 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12981 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12981 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12981 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12981,cell12981,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12981 i).lower ∧
    (cell12981 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12981 i).upper ≤ (0.532 : ℝ) ∧
    (cell12981 i).centre ≤ (0.1 : ℝ) ∧ (cell12981 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12981 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12981 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12981

/-! The local source numeric instances at 12981 have no network premises. -/
namespace BstLean.Part269.N12981
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12981)
open BstLean.Part268 (cell12981)

noncomputable def sourceNumerics12981 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12981 (cell12981 i)
      scalarRow12981.M scalarRow12981.H scalarRow12981.xi := by
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
    energy_allowance := scalarRow12981.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12981]
    centre_nonneg := (scalarRow12981.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D25.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12981])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12981
/-! Actual 12982 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12982
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12982 ≤ (1.035414752718 : ℝ) := by
  have hr : (113.938579945512 : ℝ) ≤ √(12982 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.938579945512 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12982 12982 (11 / 1000) ≤
    (0.008389493267 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12982) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.938579945512 : ℝ) ≤ √(12982 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12982)
  have hdiv : K / √(12982 : ℝ) ≤ K / 113.938579945512 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.938579945512 ≤ (0.008389493267 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12982.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12982 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12982 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12982 := gPlus_lower 12982
end BstLean.Part269.N12982

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12982
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035414752717 : ℝ) ≤ wn 12982 := by
  have hn : √(12982 : ℝ) ≤ 113.938579945513 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12982 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.938579945513 ≤ 2 / √(12982 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000246315575 : ℝ) ≤ rhoBar 12982 BstLean.Part154.csC ∧
    rhoBar 12982 BstLean.Part154.csC ≤ 0.000246315957 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035414752717 : ℝ) / (1.295212 * 12982) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035414752718 : ℝ) / (1.29521 * 12982) := by gcongr
      _ ≤ (0.000246315957 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12982 BstLean.Part154.csC) ≤ 0.000985324500 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12982 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12982 BstLean.Part154.csC) (piBar (rhoBar 12982 BstLean.Part154.csC)) ≤ 0.000188137596 ∧
    cc1 (rhoBar 12982 BstLean.Part154.csC) (piBar (rhoBar 12982 BstLean.Part154.csC)) ≤ 0.000119713241 ∧
    cc2 (rhoBar 12982 BstLean.Part154.csC) ≤ 0.000069494502 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12982 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12982 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12982 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12982 BstLean.Part154.csC * nuR (rhoBar 12982 BstLean.Part154.csC)) ≤ 0.000492647082 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000246315957 : ℝ) * 0.000985324500 := by gcongr
      _ ≤ (0.000492647082 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12982 BstLean.Part154.csC) * nuR (rhoBar 12982 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000985324500 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12982 BstLean.Part154.csC) * rhoBar 12982 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000246315957 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000246315957 / 2 + 0.399 * 0.000985324500 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000188137596 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000492647082 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119713241 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000246315957 / 1.414213562 := by gcongr
      _ ≤ (0.000069494502 : ℝ) := by norm_num

end BstLean.Part269.N12982

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12982
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12982 BstLean.Part154.csC) (piBar (rhoBar 12982 BstLean.Part154.csC)) ≤ 1.52858E-7 := by
  have hr0 : 0 ≤ rhoBar 12982 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12982 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12982 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12982 BstLean.Part154.csC) (piBar (rhoBar 12982 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12982 BstLean.Part154.csC) (piBar (rhoBar 12982 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12982 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000188137596 : ℝ) ^ 2 + 0.000119713241 ^ 2 + 3 * 0.000069494502 ^ 2 +
        2 * 0.797885 * 0.000188137596 * 0.000119713241 + 2 * 0.000188137596 * 0.000069494502 +
        4 * 0.797885 * 0.000119713241 * 0.000069494502 := by gcongr
    _ ≤ (1.52858E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12982 BstLean.Part154.csC Θ ≤ 0.002570222014 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12982 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12982 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12982 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12982 BstLean.Part154.csC) (piBar (rhoBar 12982 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12982 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035414752718 * 1.52858E-7 / (0.000246315575 : ℝ) := by gcongr
    _ ≤ 0.002570222014 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12982 BstLean.Part154.csC Θ ≤ 0.002850703116 + 0.000649452064 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12982 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12982 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12982 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035414752718 : ℝ) * ((2 * Θ * 0.000246315957 +
        (6863 / 10000) * 0.000246315957 * 12982 * 0.000985324500) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002850703116 + 0.000649452064 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12982 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12982 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12982 0.011 Θ ∧ gammaRatio 12982 0.011 Θ ≤ 0.000084677057 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12982 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035414752718 : ℝ) * 0.525 / ((1 - 0.011) * 12982) := by gcongr
      _ ≤ (0.000084677057 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12982 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12982 0.011 Θ) :=
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
    badAllowance 12982 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000421835223 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12982 BstLean.Part154.csC) 1.22 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 2 (rhoBar 12982 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12982 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12982 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12982 0.011 Θ) 1.12 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 1 (gammaRatio 12982 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12982 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12982 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12982 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12982 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035414752718 : ℝ) * 12982 *
        (1.5230E-8 / 1.1045361 + 1.8602E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000421835223 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12982 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003272538339 + 0.003219674078 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12982

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12982
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12982 BstLean.Part154.csC) (piBar (rhoBar 12982 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12982 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12982 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12982 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12982 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12982 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12982 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12982 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12982 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12982 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12982 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12982 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12982 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12982 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12982 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051904993527 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12982) ≤ 0.010481415353 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12982 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035414752718)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010481415353 + 2 * 0.737676 / 12982) := by gcongr
    _ ≤ (0.051904993527 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12982 12 ≤ 0.0015 := by
  exact BstLean.Part269.S25.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12982

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12982
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560516044145 : ℝ) ≤ plow 12982 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12982) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052469467230)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001349366558) : eMP 12982 0.011 xi bn ≤ 0.001162052818 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12982 : ℝ) * (1 - 0.011))) ≤ 0.000574607094 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001349366558 / (12982 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000574607094 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000574607094 : ℝ) + 3.141593 * 0.052469467230 / (12982 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001162052818 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052469467230)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001349366558) : PiBarMP 12982 12 0.011 xi bn ≤ 0.159472662336 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12982 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036733725077 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.310184890856 : ℝ) ≤ √((12982 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.938579945512 : ℝ) ≤ √(12982 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12982) ≤ 0.122279988652 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036733725077 + 0.052469467230 * 1.772454 / (2 * (113.310184890856 : ℝ))) * (1 + 0.001162052818) +
        8 / (12982 * 113.938579945512) + 0.122279988652 := by gcongr
    _ ≤ (0.159472662336 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052469467230)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001349366558) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280967140619) :
    parallelOracle 12982 0.011 xi bn cd ≤ 0.160441504978 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12982 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12982 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560516044145 : ℝ) ≤ plow 12982 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.938579945512 : ℝ) ≤ √(12982 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280967140619 : ℝ) / (2 * 0.560516044145 * 113.938579945512)) * 0.159472662336 +
        0.280967140619 ^ 2 / (2 * 0.560516044145 * 113.938579945512) := by gcongr
    _ ≤ (0.160441504978 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052469467230) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001349366558)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280967140619) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12982 12982 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560516044145 : ℝ) ≤ plow 12982 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.938579945512 : ℝ) ≤ √(12982 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12982 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12982 Θ 1.22 ≤ 0.011638731154 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.938579945512 := by gcongr <;> linarith
      _ ≤ (0.011638731154 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12982 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12982 12982 0.011 ≤ 0.008389493267 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12982 12982 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12982 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12982 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12982 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12982 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160441504978 + 0.011638731154 + (0.008389493267 : ℝ) *
        (1 + 2 * (0.280967140619 + 0.011638731154) / (0.560516044145 * 113.938579945512))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12982]

end BstLean.Part269.N12982

/-! The original eight local profiles supply actual 12982 moment certificates. -/
namespace BstLean.Part269.N12982
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12982 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12982 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12982 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052469467230 ∧
    0 ≤ bN 12982 BstLean.Part154.csC (groupTheta g) ∧ bN 12982 BstLean.Part154.csC (groupTheta g) ≤ 0.001349366558 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12982 12982 0.011
      (momentAllowance 12982 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12982 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12982 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12982 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12982 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12982 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229062147092 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12982 0.011
      (momentAllowance 12982 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12982 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12982
/-! The actual computed-centre upper energy formula at 12982. -/
namespace BstLean.Part269.N12982
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12982

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12982
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12982)
open BstLean.Part268 (cell12982)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084707381463
  | 2 => 0.085636681559
  | 3 => 0.086562286481
  | 4 => 0.087485182970
  | 5 => 0.088406577270
  | 6 => 0.089327929314
  | 7 => 0.090250990429
  | 8 => 0.091177844654
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12982 12982 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12982 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003274156000 + 0.003221457154 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S25.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12982

/-! Actual upper energy certificates on all 43 source endpoints at 12982. -/
namespace BstLean.Part269.N12982
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12982)
open BstLean.Part268 (cell12982)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12982 (gMinus 12982) (1 - (cell12982 i).lower) ≤ 1 ∧
    energyUpper 12982 (gMinus 12982) (BstLean.Part211.gPlus 12982)
      (finiteEnergy 12982 12982 0.011) (1 - (cell12982 i).lower) ≤
      (cell12982 i).energy := by
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
      have E := BstLean.Part269.S25.uniformEnergy10 (n := 12982) (by norm_num)
        (q := 1 - (cell12982 ⟨10,by decide⟩).lower)
        (by norm_num [cell12982]) (by norm_num [cell12982])
      exact ⟨E.1,E.2.trans (by norm_num [cell12982])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy11 (n := 12982) (by norm_num)
        (q := 1 - (cell12982 ⟨11,by decide⟩).lower)
        (by norm_num [cell12982]) (by norm_num [cell12982])
      exact ⟨E.1,E.2.trans (by norm_num [cell12982])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy12 (n := 12982) (by norm_num)
        (q := 1 - (cell12982 ⟨12,by decide⟩).lower)
        (by norm_num [cell12982]) (by norm_num [cell12982])
      exact ⟨E.1,E.2.trans (by norm_num [cell12982])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy13 (n := 12982) (by norm_num)
        (q := 1 - (cell12982 ⟨13,by decide⟩).lower)
        (by norm_num [cell12982]) (by norm_num [cell12982])
      exact ⟨E.1,E.2.trans (by norm_num [cell12982])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy14 (n := 12982) (by norm_num)
        (q := 1 - (cell12982 ⟨14,by decide⟩).lower)
        (by norm_num [cell12982]) (by norm_num [cell12982])
      exact ⟨E.1,E.2.trans (by norm_num [cell12982])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy15 (n := 12982) (by norm_num)
        (q := 1 - (cell12982 ⟨15,by decide⟩).lower)
        (by norm_num [cell12982]) (by norm_num [cell12982])
      exact ⟨E.1,E.2.trans (by norm_num [cell12982])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy16 (n := 12982) (by norm_num)
        (q := 1 - (cell12982 ⟨16,by decide⟩).lower)
        (by norm_num [cell12982]) (by norm_num [cell12982])
      exact ⟨E.1,E.2.trans (by norm_num [cell12982])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy17 (n := 12982) (by norm_num)
        (q := 1 - (cell12982 ⟨17,by decide⟩).lower)
        (by norm_num [cell12982]) (by norm_num [cell12982])
      exact ⟨E.1,E.2.trans (by norm_num [cell12982])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy18 (n := 12982) (by norm_num)
        (q := 1 - (cell12982 ⟨18,by decide⟩).lower)
        (by norm_num [cell12982]) (by norm_num [cell12982])
      exact ⟨E.1,E.2.trans (by norm_num [cell12982])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy19 (n := 12982) (by norm_num)
        (q := 1 - (cell12982 ⟨19,by decide⟩).lower)
        (by norm_num [cell12982]) (by norm_num [cell12982])
      exact ⟨E.1,E.2.trans (by norm_num [cell12982])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy20 (n := 12982) (by norm_num)
        (q := 1 - (cell12982 ⟨20,by decide⟩).lower)
        (by norm_num [cell12982]) (by norm_num [cell12982])
      exact ⟨E.1,E.2.trans (by norm_num [cell12982])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy21 (n := 12982) (by norm_num)
        (q := 1 - (cell12982 ⟨21,by decide⟩).lower)
        (by norm_num [cell12982]) (by norm_num [cell12982])
      exact ⟨E.1,E.2.trans (by norm_num [cell12982])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy22 (n := 12982) (by norm_num)
        (q := 1 - (cell12982 ⟨22,by decide⟩).lower)
        (by norm_num [cell12982]) (by norm_num [cell12982])
      exact ⟨E.1,E.2.trans (by norm_num [cell12982])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy23 (n := 12982) (by norm_num)
        (q := 1 - (cell12982 ⟨23,by decide⟩).lower)
        (by norm_num [cell12982]) (by norm_num [cell12982])
      exact ⟨E.1,E.2.trans (by norm_num [cell12982])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy24 (n := 12982) (by norm_num)
        (q := 1 - (cell12982 ⟨24,by decide⟩).lower)
        (by norm_num [cell12982]) (by norm_num [cell12982])
      exact ⟨E.1,E.2.trans (by norm_num [cell12982])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy25 (n := 12982) (by norm_num)
        (q := 1 - (cell12982 ⟨25,by decide⟩).lower)
        (by norm_num [cell12982]) (by norm_num [cell12982])
      exact ⟨E.1,E.2.trans (by norm_num [cell12982])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy26 (n := 12982) (by norm_num)
        (q := 1 - (cell12982 ⟨26,by decide⟩).lower)
        (by norm_num [cell12982]) (by norm_num [cell12982])
      exact ⟨E.1,E.2.trans (by norm_num [cell12982])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy27 (n := 12982) (by norm_num)
        (q := 1 - (cell12982 ⟨27,by decide⟩).lower)
        (by norm_num [cell12982]) (by norm_num [cell12982])
      exact ⟨E.1,E.2.trans (by norm_num [cell12982])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy28 (n := 12982) (by norm_num)
        (q := 1 - (cell12982 ⟨28,by decide⟩).lower)
        (by norm_num [cell12982]) (by norm_num [cell12982])
      exact ⟨E.1,E.2.trans (by norm_num [cell12982])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy29 (n := 12982) (by norm_num)
        (q := 1 - (cell12982 ⟨29,by decide⟩).lower)
        (by norm_num [cell12982]) (by norm_num [cell12982])
      exact ⟨E.1,E.2.trans (by norm_num [cell12982])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy30 (n := 12982) (by norm_num)
        (q := 1 - (cell12982 ⟨30,by decide⟩).lower)
        (by norm_num [cell12982]) (by norm_num [cell12982])
      exact ⟨E.1,E.2.trans (by norm_num [cell12982])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy31 (n := 12982) (by norm_num)
        (q := 1 - (cell12982 ⟨31,by decide⟩).lower)
        (by norm_num [cell12982]) (by norm_num [cell12982])
      exact ⟨E.1,E.2.trans (by norm_num [cell12982])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy32 (n := 12982) (by norm_num)
        (q := 1 - (cell12982 ⟨32,by decide⟩).lower)
        (by norm_num [cell12982]) (by norm_num [cell12982])
      exact ⟨E.1,E.2.trans (by norm_num [cell12982])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy33 (n := 12982) (by norm_num)
        (q := 1 - (cell12982 ⟨33,by decide⟩).lower)
        (by norm_num [cell12982]) (by norm_num [cell12982])
      exact ⟨E.1,E.2.trans (by norm_num [cell12982])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy34 (n := 12982) (by norm_num)
        (q := 1 - (cell12982 ⟨34,by decide⟩).lower)
        (by norm_num [cell12982]) (by norm_num [cell12982])
      exact ⟨E.1,E.2.trans (by norm_num [cell12982])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy35 (n := 12982) (by norm_num)
        (q := 1 - (cell12982 ⟨35,by decide⟩).lower)
        (by norm_num [cell12982]) (by norm_num [cell12982])
      exact ⟨E.1,E.2.trans (by norm_num [cell12982])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy36 (n := 12982) (by norm_num)
        (q := 1 - (cell12982 ⟨36,by decide⟩).lower)
        (by norm_num [cell12982]) (by norm_num [cell12982])
      exact ⟨E.1,E.2.trans (by norm_num [cell12982])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy37 (n := 12982) (by norm_num)
        (q := 1 - (cell12982 ⟨37,by decide⟩).lower)
        (by norm_num [cell12982]) (by norm_num [cell12982])
      exact ⟨E.1,E.2.trans (by norm_num [cell12982])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy38 (n := 12982) (by norm_num)
        (q := 1 - (cell12982 ⟨38,by decide⟩).lower)
        (by norm_num [cell12982]) (by norm_num [cell12982])
      exact ⟨E.1,E.2.trans (by norm_num [cell12982])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy39 (n := 12982) (by norm_num)
        (q := 1 - (cell12982 ⟨39,by decide⟩).lower)
        (by norm_num [cell12982]) (by norm_num [cell12982])
      exact ⟨E.1,E.2.trans (by norm_num [cell12982])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy40 (n := 12982) (by norm_num)
        (q := 1 - (cell12982 ⟨40,by decide⟩).lower)
        (by norm_num [cell12982]) (by norm_num [cell12982])
      exact ⟨E.1,E.2.trans (by norm_num [cell12982])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy41 (n := 12982) (by norm_num)
        (q := 1 - (cell12982 ⟨41,by decide⟩).lower)
        (by norm_num [cell12982]) (by norm_num [cell12982])
      exact ⟨E.1,E.2.trans (by norm_num [cell12982])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy42 (n := 12982) (by norm_num)
        (q := 1 - (cell12982 ⟨42,by decide⟩).lower)
        (by norm_num [cell12982]) (by norm_num [cell12982])
      exact ⟨E.1,E.2.trans (by norm_num [cell12982])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy43 (n := 12982) (by norm_num)
        (q := 1 - (cell12982 ⟨43,by decide⟩).lower)
        (by norm_num [cell12982]) (by norm_num [cell12982])
      exact ⟨E.1,E.2.trans (by norm_num [cell12982])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy44 (n := 12982) (by norm_num)
        (q := 1 - (cell12982 ⟨44,by decide⟩).lower)
        (by norm_num [cell12982]) (by norm_num [cell12982])
      exact ⟨E.1,E.2.trans (by norm_num [cell12982])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy45 (n := 12982) (by norm_num)
        (q := 1 - (cell12982 ⟨45,by decide⟩).lower)
        (by norm_num [cell12982]) (by norm_num [cell12982])
      exact ⟨E.1,E.2.trans (by norm_num [cell12982])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy46 (n := 12982) (by norm_num)
        (q := 1 - (cell12982 ⟨46,by decide⟩).lower)
        (by norm_num [cell12982]) (by norm_num [cell12982])
      exact ⟨E.1,E.2.trans (by norm_num [cell12982])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy47 (n := 12982) (by norm_num)
        (q := 1 - (cell12982 ⟨47,by decide⟩).lower)
        (by norm_num [cell12982]) (by norm_num [cell12982])
      exact ⟨E.1,E.2.trans (by norm_num [cell12982])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy48 (n := 12982) (by norm_num)
        (q := 1 - (cell12982 ⟨48,by decide⟩).lower)
        (by norm_num [cell12982]) (by norm_num [cell12982])
      exact ⟨E.1,E.2.trans (by norm_num [cell12982])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy49 (n := 12982) (by norm_num)
        (q := 1 - (cell12982 ⟨49,by decide⟩).lower)
        (by norm_num [cell12982]) (by norm_num [cell12982])
      exact ⟨E.1,E.2.trans (by norm_num [cell12982])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy50 (n := 12982) (by norm_num)
        (q := 1 - (cell12982 ⟨50,by decide⟩).lower)
        (by norm_num [cell12982]) (by norm_num [cell12982])
      exact ⟨E.1,E.2.trans (by norm_num [cell12982])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy51 (n := 12982) (by norm_num)
        (q := 1 - (cell12982 ⟨51,by decide⟩).lower)
        (by norm_num [cell12982]) (by norm_num [cell12982])
      exact ⟨E.1,E.2.trans (by norm_num [cell12982])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy52 (n := 12982) (by norm_num)
        (q := 1 - (cell12982 ⟨52,by decide⟩).lower)
        (by norm_num [cell12982]) (by norm_num [cell12982])
      exact ⟨E.1,E.2.trans (by norm_num [cell12982])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12982

/-! Source-cell containment and simple scalar guards at 12982. -/
namespace BstLean.Part269.N12982
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12982)
open BstLean.Part268 (cell12982)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12982 ⟨10,by decide⟩).lower ∧ (cell12982 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12982 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12982 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12982 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12982 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12982 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12982,cell12982,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12982 ⟨11,by decide⟩).lower ∧ (cell12982 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12982 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12982 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12982 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12982 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12982 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12982,cell12982,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12982 ⟨12,by decide⟩).lower ∧ (cell12982 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12982 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12982 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12982 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12982 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12982 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12982,cell12982,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12982 ⟨13,by decide⟩).lower ∧ (cell12982 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12982 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12982 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12982 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12982 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12982 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12982,cell12982,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12982 ⟨14,by decide⟩).lower ∧ (cell12982 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12982 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12982 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12982 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12982 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12982 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12982,cell12982,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12982 ⟨15,by decide⟩).lower ∧ (cell12982 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12982 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12982 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12982 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12982 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12982 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12982,cell12982,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12982 ⟨16,by decide⟩).lower ∧ (cell12982 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12982 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12982 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12982 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12982 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12982 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12982,cell12982,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12982 ⟨17,by decide⟩).lower ∧ (cell12982 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12982 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12982 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12982 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12982 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12982 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12982,cell12982,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12982 ⟨18,by decide⟩).lower ∧ (cell12982 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12982 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12982 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12982 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12982 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12982 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12982,cell12982,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12982 ⟨19,by decide⟩).lower ∧ (cell12982 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12982 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12982 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12982 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12982 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12982 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12982,cell12982,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12982 ⟨20,by decide⟩).lower ∧ (cell12982 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12982 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12982 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12982 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12982 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12982 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12982,cell12982,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12982 ⟨21,by decide⟩).lower ∧ (cell12982 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12982 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12982 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12982 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12982 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12982 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12982,cell12982,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12982 ⟨22,by decide⟩).lower ∧ (cell12982 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12982 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12982 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12982 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12982 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12982 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12982,cell12982,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12982 ⟨23,by decide⟩).lower ∧ (cell12982 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12982 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12982 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12982 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12982 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12982 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12982,cell12982,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12982 ⟨24,by decide⟩).lower ∧ (cell12982 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12982 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12982 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12982 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12982 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12982 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12982,cell12982,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12982 ⟨25,by decide⟩).lower ∧ (cell12982 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12982 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12982 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12982 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12982 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12982 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12982,cell12982,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12982 ⟨26,by decide⟩).lower ∧ (cell12982 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12982 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12982 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12982 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12982 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12982 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12982,cell12982,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12982 ⟨27,by decide⟩).lower ∧ (cell12982 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12982 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12982 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12982 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12982 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12982 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12982,cell12982,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12982 ⟨28,by decide⟩).lower ∧ (cell12982 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12982 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12982 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12982 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12982 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12982 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12982,cell12982,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12982 ⟨29,by decide⟩).lower ∧ (cell12982 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12982 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12982 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12982 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12982 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12982 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12982,cell12982,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12982 ⟨30,by decide⟩).lower ∧ (cell12982 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12982 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12982 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12982 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12982 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12982 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12982,cell12982,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12982 ⟨31,by decide⟩).lower ∧ (cell12982 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12982 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12982 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12982 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12982 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12982 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12982,cell12982,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12982 ⟨32,by decide⟩).lower ∧ (cell12982 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12982 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12982 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12982 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12982 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12982 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12982,cell12982,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12982 ⟨33,by decide⟩).lower ∧ (cell12982 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12982 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12982 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12982 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12982 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12982 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12982,cell12982,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12982 ⟨34,by decide⟩).lower ∧ (cell12982 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12982 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12982 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12982 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12982 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12982 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12982,cell12982,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12982 ⟨35,by decide⟩).lower ∧ (cell12982 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12982 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12982 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12982 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12982 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12982 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12982,cell12982,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12982 ⟨36,by decide⟩).lower ∧ (cell12982 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12982 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12982 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12982 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12982 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12982 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12982,cell12982,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12982 ⟨37,by decide⟩).lower ∧ (cell12982 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12982 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12982 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12982 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12982 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12982 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12982,cell12982,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12982 ⟨38,by decide⟩).lower ∧ (cell12982 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12982 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12982 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12982 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12982 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12982 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12982,cell12982,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12982 ⟨39,by decide⟩).lower ∧ (cell12982 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12982 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12982 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12982 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12982 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12982 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12982,cell12982,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12982 ⟨40,by decide⟩).lower ∧ (cell12982 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12982 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12982 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12982 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12982 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12982 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12982,cell12982,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12982 ⟨41,by decide⟩).lower ∧ (cell12982 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12982 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12982 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12982 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12982 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12982 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12982,cell12982,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12982 ⟨42,by decide⟩).lower ∧ (cell12982 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12982 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12982 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12982 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12982 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12982 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12982,cell12982,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12982 ⟨43,by decide⟩).lower ∧ (cell12982 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12982 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12982 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12982 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12982 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12982 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12982,cell12982,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12982 ⟨44,by decide⟩).lower ∧ (cell12982 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12982 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12982 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12982 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12982 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12982 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12982,cell12982,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12982 ⟨45,by decide⟩).lower ∧ (cell12982 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12982 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12982 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12982 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12982 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12982 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12982,cell12982,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12982 ⟨46,by decide⟩).lower ∧ (cell12982 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12982 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12982 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12982 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12982 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12982 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12982,cell12982,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12982 ⟨47,by decide⟩).lower ∧ (cell12982 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12982 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12982 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12982 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12982 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12982 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12982,cell12982,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12982 ⟨48,by decide⟩).lower ∧ (cell12982 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12982 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12982 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12982 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12982 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12982 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12982,cell12982,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12982 ⟨49,by decide⟩).lower ∧ (cell12982 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12982 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12982 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12982 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12982 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12982 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12982,cell12982,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12982 ⟨50,by decide⟩).lower ∧ (cell12982 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12982 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12982 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12982 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12982 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12982 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12982,cell12982,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12982 ⟨51,by decide⟩).lower ∧ (cell12982 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12982 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12982 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12982 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12982 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12982 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12982,cell12982,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12982 ⟨52,by decide⟩).lower ∧ (cell12982 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12982 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12982 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12982 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12982 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12982 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12982,cell12982,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12982 i).lower ∧
    (cell12982 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12982 i).upper ≤ (0.532 : ℝ) ∧
    (cell12982 i).centre ≤ (0.1 : ℝ) ∧ (cell12982 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12982 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12982 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12982

/-! The local source numeric instances at 12982 have no network premises. -/
namespace BstLean.Part269.N12982
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12982)
open BstLean.Part268 (cell12982)

noncomputable def sourceNumerics12982 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12982 (cell12982 i)
      scalarRow12982.M scalarRow12982.H scalarRow12982.xi := by
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
    energy_allowance := scalarRow12982.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12982]
    centre_nonneg := (scalarRow12982.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D25.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12982])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12982
/-! Actual 12983 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12983
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12983 ≤ (1.035413376937 : ℝ) := by
  have hr : (113.942968190231 : ℝ) ≤ √(12983 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.942968190231 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12983 12983 (11 / 1000) ≤
    (0.008389170163 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12983) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.942968190231 : ℝ) ≤ √(12983 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12983)
  have hdiv : K / √(12983 : ℝ) ≤ K / 113.942968190231 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.942968190231 ≤ (0.008389170163 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12983.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12983 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12983 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12983 := gPlus_lower 12983
end BstLean.Part269.N12983

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12983
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035413376936 : ℝ) ≤ wn 12983 := by
  have hn : √(12983 : ℝ) ≤ 113.942968190232 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12983 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.942968190232 ≤ 2 / √(12983 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000246296276 : ℝ) ≤ rhoBar 12983 BstLean.Part154.csC ∧
    rhoBar 12983 BstLean.Part154.csC ≤ 0.000246296657 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035413376936 : ℝ) / (1.295212 * 12983) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035413376937 : ℝ) / (1.29521 * 12983) := by gcongr
      _ ≤ (0.000246296657 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12983 BstLean.Part154.csC) ≤ 0.000985247291 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12983 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12983 BstLean.Part154.csC) (piBar (rhoBar 12983 BstLean.Part154.csC)) ≤ 0.000188122854 ∧
    cc1 (rhoBar 12983 BstLean.Part154.csC) (piBar (rhoBar 12983 BstLean.Part154.csC)) ≤ 0.000119703861 ∧
    cc2 (rhoBar 12983 BstLean.Part154.csC) ≤ 0.000069489057 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12983 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12983 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12983 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12983 BstLean.Part154.csC * nuR (rhoBar 12983 BstLean.Part154.csC)) ≤ 0.000492608480 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000246296657 : ℝ) * 0.000985247291 := by gcongr
      _ ≤ (0.000492608480 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12983 BstLean.Part154.csC) * nuR (rhoBar 12983 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000985247291 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12983 BstLean.Part154.csC) * rhoBar 12983 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000246296657 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000246296657 / 2 + 0.399 * 0.000985247291 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000188122854 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000492608480 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119703861 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000246296657 / 1.414213562 := by gcongr
      _ ≤ (0.000069489057 : ℝ) := by norm_num

end BstLean.Part269.N12983

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12983
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12983 BstLean.Part154.csC) (piBar (rhoBar 12983 BstLean.Part154.csC)) ≤ 1.52834E-7 := by
  have hr0 : 0 ≤ rhoBar 12983 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12983 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12983 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12983 BstLean.Part154.csC) (piBar (rhoBar 12983 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12983 BstLean.Part154.csC) (piBar (rhoBar 12983 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12983 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000188122854 : ℝ) ^ 2 + 0.000119703861 ^ 2 + 3 * 0.000069489057 ^ 2 +
        2 * 0.797885 * 0.000188122854 * 0.000119703861 + 2 * 0.000188122854 * 0.000069489057 +
        4 * 0.797885 * 0.000119703861 * 0.000069489057 := by gcongr
    _ ≤ (1.52834E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12983 BstLean.Part154.csC Θ ≤ 0.002570016415 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12983 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12983 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12983 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12983 BstLean.Part154.csC) (piBar (rhoBar 12983 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12983 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035413376937 * 1.52834E-7 / (0.000246296276 : ℝ) := by gcongr
    _ ≤ 0.002570016415 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12983 BstLean.Part154.csC Θ ≤ 0.002850472156 + 0.000649400313 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12983 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12983 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12983 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035413376937 : ℝ) * ((2 * Θ * 0.000246296657 +
        (6863 / 10000) * 0.000246296657 * 12983 * 0.000985247291) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002850472156 + 0.000649400313 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12983 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12983 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12983 0.011 Θ ∧ gammaRatio 12983 0.011 Θ ≤ 0.000084670422 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12983 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035413376937 : ℝ) * 0.525 / ((1 - 0.011) * 12983) := by gcongr
      _ ≤ (0.000084670422 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12983 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12983 0.011 Θ) :=
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
    badAllowance 12983 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000421835223 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12983 BstLean.Part154.csC) 1.22 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 2 (rhoBar 12983 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12983 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12983 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12983 0.011 Θ) 1.12 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 1 (gammaRatio 12983 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12983 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12983 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12983 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12983 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035413376937 : ℝ) * 12983 *
        (1.5230E-8 / 1.1045361 + 1.8602E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000421835223 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12983 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003272307379 + 0.003219416728 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12983

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12983
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12983 BstLean.Part154.csC) (piBar (rhoBar 12983 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12983 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12983 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12983 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12983 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12983 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12983 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12983 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12983 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12983 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12983 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12983 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12983 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12983 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12983 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051902973088 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12983) ≤ 0.010481011686 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12983 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035413376937)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010481011686 + 2 * 0.737676 / 12983) := by gcongr
    _ ≤ (0.051902973088 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12983 12 ≤ 0.0015 := by
  exact BstLean.Part269.S25.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12983

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12983
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560516087422 : ℝ) ≤ plow 12983 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12983) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052469101162)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001349258618) : eMP 12983 0.011 xi bn ≤ 0.001161961518 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12983 : ℝ) * (1 - 0.011))) ≤ 0.000574561983 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001349258618 / (12983 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000574561983 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000574561983 : ℝ) + 3.141593 * 0.052469101162 / (12983 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001161961518 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052469101162)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001349258618) : PiBarMP 12983 12 0.011 xi bn ≤ 0.159466459347 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12983 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036732255826 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.314548933488 : ℝ) ≤ √((12983 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.942968190231 : ℝ) ≤ √(12983 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12983) ≤ 0.122275279327 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036732255826 + 0.052469101162 * 1.772454 / (2 * (113.314548933488 : ℝ))) * (1 + 0.001161961518) +
        8 / (12983 * 113.942968190231) + 0.122275279327 := by gcongr
    _ ≤ (0.159466459347 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052469101162)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001349258618) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280964321120) :
    parallelOracle 12983 0.011 xi bn cd ≤ 0.160435235033 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12983 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12983 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560516087422 : ℝ) ≤ plow 12983 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.942968190231 : ℝ) ≤ √(12983 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280964321120 : ℝ) / (2 * 0.560516087422 * 113.942968190231)) * 0.159466459347 +
        0.280964321120 ^ 2 / (2 * 0.560516087422 * 113.942968190231) := by gcongr
    _ ≤ (0.160435235033 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052469101162) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001349258618)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280964321120) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12983 12983 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560516087422 : ℝ) ≤ plow 12983 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.942968190231 : ℝ) ≤ √(12983 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12983 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12983 Θ 1.22 ≤ 0.011638282916 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.942968190231 := by gcongr <;> linarith
      _ ≤ (0.011638282916 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12983 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12983 12983 0.011 ≤ 0.008389170163 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12983 12983 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12983 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12983 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12983 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12983 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160435235033 + 0.011638282916 + (0.008389170163 : ℝ) *
        (1 + 2 * (0.280964321120 + 0.011638282916) / (0.560516087422 * 113.942968190231))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12983]

end BstLean.Part269.N12983

/-! The original eight local profiles supply actual 12983 moment certificates. -/
namespace BstLean.Part269.N12983
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12983 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12983 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12983 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052469101162 ∧
    0 ≤ bN 12983 BstLean.Part154.csC (groupTheta g) ∧ bN 12983 BstLean.Part154.csC (groupTheta g) ≤ 0.001349258618 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12983 12983 0.011
      (momentAllowance 12983 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12983 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12983 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12983 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12983 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12983 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229061348032 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12983 0.011
      (momentAllowance 12983 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12983 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12983
/-! The actual computed-centre upper energy formula at 12983. -/
namespace BstLean.Part269.N12983
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12983

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12983
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12983)
open BstLean.Part268 (cell12983)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084704748601
  | 2 => 0.085634013630
  | 3 => 0.086559578103
  | 4 => 0.087482427507
  | 5 => 0.088403766599
  | 6 => 0.089325053568
  | 7 => 0.090248037710
  | 8 => 0.091174800706
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12983 12983 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12983 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003274156000 + 0.003221457154 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S25.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12983

/-! Actual upper energy certificates on all 43 source endpoints at 12983. -/
namespace BstLean.Part269.N12983
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12983)
open BstLean.Part268 (cell12983)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12983 (gMinus 12983) (1 - (cell12983 i).lower) ≤ 1 ∧
    energyUpper 12983 (gMinus 12983) (BstLean.Part211.gPlus 12983)
      (finiteEnergy 12983 12983 0.011) (1 - (cell12983 i).lower) ≤
      (cell12983 i).energy := by
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
      have E := BstLean.Part269.S25.uniformEnergy10 (n := 12983) (by norm_num)
        (q := 1 - (cell12983 ⟨10,by decide⟩).lower)
        (by norm_num [cell12983]) (by norm_num [cell12983])
      exact ⟨E.1,E.2.trans (by norm_num [cell12983])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy11 (n := 12983) (by norm_num)
        (q := 1 - (cell12983 ⟨11,by decide⟩).lower)
        (by norm_num [cell12983]) (by norm_num [cell12983])
      exact ⟨E.1,E.2.trans (by norm_num [cell12983])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy12 (n := 12983) (by norm_num)
        (q := 1 - (cell12983 ⟨12,by decide⟩).lower)
        (by norm_num [cell12983]) (by norm_num [cell12983])
      exact ⟨E.1,E.2.trans (by norm_num [cell12983])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy13 (n := 12983) (by norm_num)
        (q := 1 - (cell12983 ⟨13,by decide⟩).lower)
        (by norm_num [cell12983]) (by norm_num [cell12983])
      exact ⟨E.1,E.2.trans (by norm_num [cell12983])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy14 (n := 12983) (by norm_num)
        (q := 1 - (cell12983 ⟨14,by decide⟩).lower)
        (by norm_num [cell12983]) (by norm_num [cell12983])
      exact ⟨E.1,E.2.trans (by norm_num [cell12983])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy15 (n := 12983) (by norm_num)
        (q := 1 - (cell12983 ⟨15,by decide⟩).lower)
        (by norm_num [cell12983]) (by norm_num [cell12983])
      exact ⟨E.1,E.2.trans (by norm_num [cell12983])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy16 (n := 12983) (by norm_num)
        (q := 1 - (cell12983 ⟨16,by decide⟩).lower)
        (by norm_num [cell12983]) (by norm_num [cell12983])
      exact ⟨E.1,E.2.trans (by norm_num [cell12983])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy17 (n := 12983) (by norm_num)
        (q := 1 - (cell12983 ⟨17,by decide⟩).lower)
        (by norm_num [cell12983]) (by norm_num [cell12983])
      exact ⟨E.1,E.2.trans (by norm_num [cell12983])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy18 (n := 12983) (by norm_num)
        (q := 1 - (cell12983 ⟨18,by decide⟩).lower)
        (by norm_num [cell12983]) (by norm_num [cell12983])
      exact ⟨E.1,E.2.trans (by norm_num [cell12983])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy19 (n := 12983) (by norm_num)
        (q := 1 - (cell12983 ⟨19,by decide⟩).lower)
        (by norm_num [cell12983]) (by norm_num [cell12983])
      exact ⟨E.1,E.2.trans (by norm_num [cell12983])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy20 (n := 12983) (by norm_num)
        (q := 1 - (cell12983 ⟨20,by decide⟩).lower)
        (by norm_num [cell12983]) (by norm_num [cell12983])
      exact ⟨E.1,E.2.trans (by norm_num [cell12983])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy21 (n := 12983) (by norm_num)
        (q := 1 - (cell12983 ⟨21,by decide⟩).lower)
        (by norm_num [cell12983]) (by norm_num [cell12983])
      exact ⟨E.1,E.2.trans (by norm_num [cell12983])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy22 (n := 12983) (by norm_num)
        (q := 1 - (cell12983 ⟨22,by decide⟩).lower)
        (by norm_num [cell12983]) (by norm_num [cell12983])
      exact ⟨E.1,E.2.trans (by norm_num [cell12983])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy23 (n := 12983) (by norm_num)
        (q := 1 - (cell12983 ⟨23,by decide⟩).lower)
        (by norm_num [cell12983]) (by norm_num [cell12983])
      exact ⟨E.1,E.2.trans (by norm_num [cell12983])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy24 (n := 12983) (by norm_num)
        (q := 1 - (cell12983 ⟨24,by decide⟩).lower)
        (by norm_num [cell12983]) (by norm_num [cell12983])
      exact ⟨E.1,E.2.trans (by norm_num [cell12983])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy25 (n := 12983) (by norm_num)
        (q := 1 - (cell12983 ⟨25,by decide⟩).lower)
        (by norm_num [cell12983]) (by norm_num [cell12983])
      exact ⟨E.1,E.2.trans (by norm_num [cell12983])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy26 (n := 12983) (by norm_num)
        (q := 1 - (cell12983 ⟨26,by decide⟩).lower)
        (by norm_num [cell12983]) (by norm_num [cell12983])
      exact ⟨E.1,E.2.trans (by norm_num [cell12983])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy27 (n := 12983) (by norm_num)
        (q := 1 - (cell12983 ⟨27,by decide⟩).lower)
        (by norm_num [cell12983]) (by norm_num [cell12983])
      exact ⟨E.1,E.2.trans (by norm_num [cell12983])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy28 (n := 12983) (by norm_num)
        (q := 1 - (cell12983 ⟨28,by decide⟩).lower)
        (by norm_num [cell12983]) (by norm_num [cell12983])
      exact ⟨E.1,E.2.trans (by norm_num [cell12983])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy29 (n := 12983) (by norm_num)
        (q := 1 - (cell12983 ⟨29,by decide⟩).lower)
        (by norm_num [cell12983]) (by norm_num [cell12983])
      exact ⟨E.1,E.2.trans (by norm_num [cell12983])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy30 (n := 12983) (by norm_num)
        (q := 1 - (cell12983 ⟨30,by decide⟩).lower)
        (by norm_num [cell12983]) (by norm_num [cell12983])
      exact ⟨E.1,E.2.trans (by norm_num [cell12983])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy31 (n := 12983) (by norm_num)
        (q := 1 - (cell12983 ⟨31,by decide⟩).lower)
        (by norm_num [cell12983]) (by norm_num [cell12983])
      exact ⟨E.1,E.2.trans (by norm_num [cell12983])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy32 (n := 12983) (by norm_num)
        (q := 1 - (cell12983 ⟨32,by decide⟩).lower)
        (by norm_num [cell12983]) (by norm_num [cell12983])
      exact ⟨E.1,E.2.trans (by norm_num [cell12983])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy33 (n := 12983) (by norm_num)
        (q := 1 - (cell12983 ⟨33,by decide⟩).lower)
        (by norm_num [cell12983]) (by norm_num [cell12983])
      exact ⟨E.1,E.2.trans (by norm_num [cell12983])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy34 (n := 12983) (by norm_num)
        (q := 1 - (cell12983 ⟨34,by decide⟩).lower)
        (by norm_num [cell12983]) (by norm_num [cell12983])
      exact ⟨E.1,E.2.trans (by norm_num [cell12983])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy35 (n := 12983) (by norm_num)
        (q := 1 - (cell12983 ⟨35,by decide⟩).lower)
        (by norm_num [cell12983]) (by norm_num [cell12983])
      exact ⟨E.1,E.2.trans (by norm_num [cell12983])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy36 (n := 12983) (by norm_num)
        (q := 1 - (cell12983 ⟨36,by decide⟩).lower)
        (by norm_num [cell12983]) (by norm_num [cell12983])
      exact ⟨E.1,E.2.trans (by norm_num [cell12983])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy37 (n := 12983) (by norm_num)
        (q := 1 - (cell12983 ⟨37,by decide⟩).lower)
        (by norm_num [cell12983]) (by norm_num [cell12983])
      exact ⟨E.1,E.2.trans (by norm_num [cell12983])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy38 (n := 12983) (by norm_num)
        (q := 1 - (cell12983 ⟨38,by decide⟩).lower)
        (by norm_num [cell12983]) (by norm_num [cell12983])
      exact ⟨E.1,E.2.trans (by norm_num [cell12983])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy39 (n := 12983) (by norm_num)
        (q := 1 - (cell12983 ⟨39,by decide⟩).lower)
        (by norm_num [cell12983]) (by norm_num [cell12983])
      exact ⟨E.1,E.2.trans (by norm_num [cell12983])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy40 (n := 12983) (by norm_num)
        (q := 1 - (cell12983 ⟨40,by decide⟩).lower)
        (by norm_num [cell12983]) (by norm_num [cell12983])
      exact ⟨E.1,E.2.trans (by norm_num [cell12983])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy41 (n := 12983) (by norm_num)
        (q := 1 - (cell12983 ⟨41,by decide⟩).lower)
        (by norm_num [cell12983]) (by norm_num [cell12983])
      exact ⟨E.1,E.2.trans (by norm_num [cell12983])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy42 (n := 12983) (by norm_num)
        (q := 1 - (cell12983 ⟨42,by decide⟩).lower)
        (by norm_num [cell12983]) (by norm_num [cell12983])
      exact ⟨E.1,E.2.trans (by norm_num [cell12983])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy43 (n := 12983) (by norm_num)
        (q := 1 - (cell12983 ⟨43,by decide⟩).lower)
        (by norm_num [cell12983]) (by norm_num [cell12983])
      exact ⟨E.1,E.2.trans (by norm_num [cell12983])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy44 (n := 12983) (by norm_num)
        (q := 1 - (cell12983 ⟨44,by decide⟩).lower)
        (by norm_num [cell12983]) (by norm_num [cell12983])
      exact ⟨E.1,E.2.trans (by norm_num [cell12983])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy45 (n := 12983) (by norm_num)
        (q := 1 - (cell12983 ⟨45,by decide⟩).lower)
        (by norm_num [cell12983]) (by norm_num [cell12983])
      exact ⟨E.1,E.2.trans (by norm_num [cell12983])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy46 (n := 12983) (by norm_num)
        (q := 1 - (cell12983 ⟨46,by decide⟩).lower)
        (by norm_num [cell12983]) (by norm_num [cell12983])
      exact ⟨E.1,E.2.trans (by norm_num [cell12983])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy47 (n := 12983) (by norm_num)
        (q := 1 - (cell12983 ⟨47,by decide⟩).lower)
        (by norm_num [cell12983]) (by norm_num [cell12983])
      exact ⟨E.1,E.2.trans (by norm_num [cell12983])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy48 (n := 12983) (by norm_num)
        (q := 1 - (cell12983 ⟨48,by decide⟩).lower)
        (by norm_num [cell12983]) (by norm_num [cell12983])
      exact ⟨E.1,E.2.trans (by norm_num [cell12983])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy49 (n := 12983) (by norm_num)
        (q := 1 - (cell12983 ⟨49,by decide⟩).lower)
        (by norm_num [cell12983]) (by norm_num [cell12983])
      exact ⟨E.1,E.2.trans (by norm_num [cell12983])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy50 (n := 12983) (by norm_num)
        (q := 1 - (cell12983 ⟨50,by decide⟩).lower)
        (by norm_num [cell12983]) (by norm_num [cell12983])
      exact ⟨E.1,E.2.trans (by norm_num [cell12983])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy51 (n := 12983) (by norm_num)
        (q := 1 - (cell12983 ⟨51,by decide⟩).lower)
        (by norm_num [cell12983]) (by norm_num [cell12983])
      exact ⟨E.1,E.2.trans (by norm_num [cell12983])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy52 (n := 12983) (by norm_num)
        (q := 1 - (cell12983 ⟨52,by decide⟩).lower)
        (by norm_num [cell12983]) (by norm_num [cell12983])
      exact ⟨E.1,E.2.trans (by norm_num [cell12983])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12983

/-! Source-cell containment and simple scalar guards at 12983. -/
namespace BstLean.Part269.N12983
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12983)
open BstLean.Part268 (cell12983)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12983 ⟨10,by decide⟩).lower ∧ (cell12983 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12983 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12983 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12983 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12983 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12983 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12983,cell12983,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12983 ⟨11,by decide⟩).lower ∧ (cell12983 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12983 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12983 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12983 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12983 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12983 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12983,cell12983,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12983 ⟨12,by decide⟩).lower ∧ (cell12983 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12983 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12983 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12983 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12983 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12983 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12983,cell12983,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12983 ⟨13,by decide⟩).lower ∧ (cell12983 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12983 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12983 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12983 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12983 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12983 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12983,cell12983,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12983 ⟨14,by decide⟩).lower ∧ (cell12983 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12983 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12983 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12983 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12983 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12983 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12983,cell12983,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12983 ⟨15,by decide⟩).lower ∧ (cell12983 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12983 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12983 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12983 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12983 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12983 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12983,cell12983,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12983 ⟨16,by decide⟩).lower ∧ (cell12983 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12983 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12983 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12983 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12983 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12983 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12983,cell12983,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12983 ⟨17,by decide⟩).lower ∧ (cell12983 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12983 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12983 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12983 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12983 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12983 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12983,cell12983,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12983 ⟨18,by decide⟩).lower ∧ (cell12983 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12983 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12983 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12983 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12983 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12983 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12983,cell12983,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12983 ⟨19,by decide⟩).lower ∧ (cell12983 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12983 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12983 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12983 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12983 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12983 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12983,cell12983,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12983 ⟨20,by decide⟩).lower ∧ (cell12983 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12983 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12983 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12983 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12983 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12983 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12983,cell12983,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12983 ⟨21,by decide⟩).lower ∧ (cell12983 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12983 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12983 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12983 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12983 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12983 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12983,cell12983,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12983 ⟨22,by decide⟩).lower ∧ (cell12983 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12983 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12983 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12983 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12983 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12983 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12983,cell12983,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12983 ⟨23,by decide⟩).lower ∧ (cell12983 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12983 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12983 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12983 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12983 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12983 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12983,cell12983,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12983 ⟨24,by decide⟩).lower ∧ (cell12983 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12983 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12983 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12983 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12983 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12983 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12983,cell12983,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12983 ⟨25,by decide⟩).lower ∧ (cell12983 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12983 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12983 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12983 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12983 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12983 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12983,cell12983,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12983 ⟨26,by decide⟩).lower ∧ (cell12983 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12983 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12983 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12983 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12983 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12983 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12983,cell12983,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12983 ⟨27,by decide⟩).lower ∧ (cell12983 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12983 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12983 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12983 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12983 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12983 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12983,cell12983,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12983 ⟨28,by decide⟩).lower ∧ (cell12983 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12983 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12983 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12983 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12983 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12983 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12983,cell12983,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12983 ⟨29,by decide⟩).lower ∧ (cell12983 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12983 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12983 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12983 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12983 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12983 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12983,cell12983,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12983 ⟨30,by decide⟩).lower ∧ (cell12983 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12983 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12983 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12983 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12983 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12983 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12983,cell12983,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12983 ⟨31,by decide⟩).lower ∧ (cell12983 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12983 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12983 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12983 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12983 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12983 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12983,cell12983,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12983 ⟨32,by decide⟩).lower ∧ (cell12983 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12983 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12983 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12983 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12983 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12983 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12983,cell12983,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12983 ⟨33,by decide⟩).lower ∧ (cell12983 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12983 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12983 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12983 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12983 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12983 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12983,cell12983,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12983 ⟨34,by decide⟩).lower ∧ (cell12983 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12983 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12983 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12983 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12983 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12983 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12983,cell12983,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12983 ⟨35,by decide⟩).lower ∧ (cell12983 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12983 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12983 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12983 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12983 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12983 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12983,cell12983,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12983 ⟨36,by decide⟩).lower ∧ (cell12983 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12983 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12983 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12983 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12983 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12983 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12983,cell12983,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12983 ⟨37,by decide⟩).lower ∧ (cell12983 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12983 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12983 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12983 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12983 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12983 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12983,cell12983,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12983 ⟨38,by decide⟩).lower ∧ (cell12983 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12983 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12983 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12983 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12983 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12983 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12983,cell12983,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12983 ⟨39,by decide⟩).lower ∧ (cell12983 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12983 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12983 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12983 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12983 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12983 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12983,cell12983,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12983 ⟨40,by decide⟩).lower ∧ (cell12983 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12983 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12983 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12983 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12983 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12983 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12983,cell12983,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12983 ⟨41,by decide⟩).lower ∧ (cell12983 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12983 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12983 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12983 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12983 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12983 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12983,cell12983,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12983 ⟨42,by decide⟩).lower ∧ (cell12983 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12983 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12983 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12983 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12983 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12983 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12983,cell12983,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12983 ⟨43,by decide⟩).lower ∧ (cell12983 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12983 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12983 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12983 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12983 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12983 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12983,cell12983,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12983 ⟨44,by decide⟩).lower ∧ (cell12983 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12983 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12983 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12983 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12983 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12983 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12983,cell12983,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12983 ⟨45,by decide⟩).lower ∧ (cell12983 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12983 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12983 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12983 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12983 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12983 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12983,cell12983,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12983 ⟨46,by decide⟩).lower ∧ (cell12983 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12983 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12983 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12983 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12983 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12983 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12983,cell12983,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12983 ⟨47,by decide⟩).lower ∧ (cell12983 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12983 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12983 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12983 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12983 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12983 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12983,cell12983,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12983 ⟨48,by decide⟩).lower ∧ (cell12983 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12983 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12983 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12983 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12983 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12983 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12983,cell12983,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12983 ⟨49,by decide⟩).lower ∧ (cell12983 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12983 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12983 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12983 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12983 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12983 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12983,cell12983,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12983 ⟨50,by decide⟩).lower ∧ (cell12983 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12983 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12983 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12983 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12983 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12983 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12983,cell12983,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12983 ⟨51,by decide⟩).lower ∧ (cell12983 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12983 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12983 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12983 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12983 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12983 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12983,cell12983,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12983 ⟨52,by decide⟩).lower ∧ (cell12983 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12983 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12983 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12983 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12983 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12983 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12983,cell12983,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12983 i).lower ∧
    (cell12983 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12983 i).upper ≤ (0.532 : ℝ) ∧
    (cell12983 i).centre ≤ (0.1 : ℝ) ∧ (cell12983 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12983 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12983 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12983

/-! The local source numeric instances at 12983 have no network premises. -/
namespace BstLean.Part269.N12983
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12983)
open BstLean.Part268 (cell12983)

noncomputable def sourceNumerics12983 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12983 (cell12983 i)
      scalarRow12983.M scalarRow12983.H scalarRow12983.xi := by
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
    energy_allowance := scalarRow12983.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12983]
    centre_nonneg := (scalarRow12983.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D25.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12983])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12983
/-! Actual 12984 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12984
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12984 ≤ (1.035412001315 : ℝ) := by
  have hr : (113.947356265952 : ℝ) ≤ √(12984 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.947356265952 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12984 12984 (11 / 1000) ≤
    (0.008388847096 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12984) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.947356265952 : ℝ) ≤ √(12984 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12984)
  have hdiv : K / √(12984 : ℝ) ≤ K / 113.947356265952 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.947356265952 ≤ (0.008388847096 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12984.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12984 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12984 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12984 := gPlus_lower 12984
end BstLean.Part269.N12984

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12984
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035412001314 : ℝ) ≤ wn 12984 := by
  have hn : √(12984 : ℝ) ≤ 113.947356265953 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12984 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.947356265953 ≤ 2 / √(12984 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000246276980 : ℝ) ≤ rhoBar 12984 BstLean.Part154.csC ∧
    rhoBar 12984 BstLean.Part154.csC ≤ 0.000246277361 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035412001314 : ℝ) / (1.295212 * 12984) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035412001315 : ℝ) / (1.29521 * 12984) := by gcongr
      _ ≤ (0.000246277361 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12984 BstLean.Part154.csC) ≤ 0.000985170097 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12984 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12984 BstLean.Part154.csC) (piBar (rhoBar 12984 BstLean.Part154.csC)) ≤ 0.000188108115 ∧
    cc1 (rhoBar 12984 BstLean.Part154.csC) (piBar (rhoBar 12984 BstLean.Part154.csC)) ≤ 0.000119694483 ∧
    cc2 (rhoBar 12984 BstLean.Part154.csC) ≤ 0.000069483613 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12984 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12984 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12984 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12984 BstLean.Part154.csC * nuR (rhoBar 12984 BstLean.Part154.csC)) ≤ 0.000492569886 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000246277361 : ℝ) * 0.000985170097 := by gcongr
      _ ≤ (0.000492569886 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12984 BstLean.Part154.csC) * nuR (rhoBar 12984 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000985170097 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12984 BstLean.Part154.csC) * rhoBar 12984 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000246277361 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000246277361 / 2 + 0.399 * 0.000985170097 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000188108115 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000492569886 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119694483 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000246277361 / 1.414213562 := by gcongr
      _ ≤ (0.000069483613 : ℝ) := by norm_num

end BstLean.Part269.N12984

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12984
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12984 BstLean.Part154.csC) (piBar (rhoBar 12984 BstLean.Part154.csC)) ≤ 1.52810E-7 := by
  have hr0 : 0 ≤ rhoBar 12984 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12984 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12984 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12984 BstLean.Part154.csC) (piBar (rhoBar 12984 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12984 BstLean.Part154.csC) (piBar (rhoBar 12984 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12984 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000188108115 : ℝ) ^ 2 + 0.000119694483 ^ 2 + 3 * 0.000069483613 ^ 2 +
        2 * 0.797885 * 0.000188108115 * 0.000119694483 + 2 * 0.000188108115 * 0.000069483613 +
        4 * 0.797885 * 0.000119694483 * 0.000069483613 := by gcongr
    _ ≤ (1.52810E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12984 BstLean.Part154.csC Θ ≤ 0.002569810755 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12984 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12984 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12984 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12984 BstLean.Part154.csC) (piBar (rhoBar 12984 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12984 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035412001315 * 1.52810E-7 / (0.000246276980 : ℝ) := by gcongr
    _ ≤ 0.002569810755 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12984 BstLean.Part154.csC Θ ≤ 0.002850241254 + 0.000649348573 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12984 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12984 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12984 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035412001315 : ℝ) * ((2 * Θ * 0.000246277361 +
        (6863 / 10000) * 0.000246277361 * 12984 * 0.000985170097) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002850241254 + 0.000649348573 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12984 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12984 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12984 0.011 Θ ∧ gammaRatio 12984 0.011 Θ ≤ 0.000084663788 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12984 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035412001315 : ℝ) * 0.525 / ((1 - 0.011) * 12984) := by gcongr
      _ ≤ (0.000084663788 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12984 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12984 0.011 Θ) :=
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
    badAllowance 12984 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000421835223 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12984 BstLean.Part154.csC) 1.22 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 2 (rhoBar 12984 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12984 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12984 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12984 0.011 Θ) 1.12 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 1 (gammaRatio 12984 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12984 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12984 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12984 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12984 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035412001315 : ℝ) * 12984 *
        (1.5230E-8 / 1.1045361 + 1.8602E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000421835223 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12984 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003272076477 + 0.003219159328 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12984

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12984
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12984 BstLean.Part154.csC) (piBar (rhoBar 12984 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12984 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12984 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12984 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12984 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12984 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12984 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12984 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12984 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12984 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12984 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12984 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12984 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12984 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12984 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051900952880 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12984) ≤ 0.010480608065 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12984 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035412001315)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010480608065 + 2 * 0.737676 / 12984) := by gcongr
    _ ≤ (0.051900952880 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12984 12 ≤ 0.0015 := by
  exact BstLean.Part269.S25.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12984

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12984
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560516130691 : ℝ) ≤ plow 12984 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12984) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052468735125)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001349150647) : eMP 12984 0.011 xi bn ≤ 0.001161870210 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12984 : ℝ) * (1 - 0.011))) ≤ 0.000574516868 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001349150647 / (12984 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000574516868 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000574516868 : ℝ) + 3.141593 * 0.052468735125 / (12984 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001161870210 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052468735125)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001349150647) : PiBarMP 12984 12 0.011 xi bn ≤ 0.159460256423 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12984 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036730786093 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.318912808056 : ℝ) ≤ √((12984 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.947356265952 : ℝ) ≤ √(12984 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12984) ≤ 0.122270570546 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036730786093 + 0.052468735125 * 1.772454 / (2 * (113.318912808056 : ℝ))) * (1 + 0.001161870210) +
        8 / (12984 * 113.947356265952) + 0.122270570546 := by gcongr
    _ ≤ (0.159460256423 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052468735125)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001349150647) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280961501917) :
    parallelOracle 12984 0.011 xi bn cd ≤ 0.160428965163 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12984 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12984 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560516130691 : ℝ) ≤ plow 12984 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.947356265952 : ℝ) ≤ √(12984 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280961501917 : ℝ) / (2 * 0.560516130691 * 113.947356265952)) * 0.159460256423 +
        0.280961501917 ^ 2 / (2 * 0.560516130691 * 113.947356265952) := by gcongr
    _ ≤ (0.160428965163 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052468735125) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001349150647)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280961501917) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12984 12984 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560516130691 : ℝ) ≤ plow 12984 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.947356265952 : ℝ) ≤ √(12984 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12984 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12984 Θ 1.22 ≤ 0.011637834729 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.947356265952 := by gcongr <;> linarith
      _ ≤ (0.011637834729 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12984 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12984 12984 0.011 ≤ 0.008388847096 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12984 12984 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12984 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12984 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12984 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12984 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160428965163 + 0.011637834729 + (0.008388847096 : ℝ) *
        (1 + 2 * (0.280961501917 + 0.011637834729) / (0.560516130691 * 113.947356265952))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12984]

end BstLean.Part269.N12984

/-! The original eight local profiles supply actual 12984 moment certificates. -/
namespace BstLean.Part269.N12984
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12984 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12984 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12984 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052468735125 ∧
    0 ≤ bN 12984 BstLean.Part154.csC (groupTheta g) ∧ bN 12984 BstLean.Part154.csC (groupTheta g) ≤ 0.001349150647 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12984 12984 0.011
      (momentAllowance 12984 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12984 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12984 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12984 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12984 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12984 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229060549037 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12984 0.011
      (momentAllowance 12984 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12984 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12984
/-! The actual computed-centre upper energy formula at 12984. -/
namespace BstLean.Part269.N12984
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12984

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12984
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12984)
open BstLean.Part268 (cell12984)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084702116560
  | 2 => 0.085631346550
  | 3 => 0.086556870612
  | 4 => 0.087479672974
  | 5 => 0.088400956912
  | 6 => 0.089322178875
  | 7 => 0.090245086125
  | 8 => 0.091171757990
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12984 12984 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12984 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003274156000 + 0.003221457154 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S25.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12984

/-! Actual upper energy certificates on all 43 source endpoints at 12984. -/
namespace BstLean.Part269.N12984
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12984)
open BstLean.Part268 (cell12984)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12984 (gMinus 12984) (1 - (cell12984 i).lower) ≤ 1 ∧
    energyUpper 12984 (gMinus 12984) (BstLean.Part211.gPlus 12984)
      (finiteEnergy 12984 12984 0.011) (1 - (cell12984 i).lower) ≤
      (cell12984 i).energy := by
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
      have E := BstLean.Part269.S25.uniformEnergy10 (n := 12984) (by norm_num)
        (q := 1 - (cell12984 ⟨10,by decide⟩).lower)
        (by norm_num [cell12984]) (by norm_num [cell12984])
      exact ⟨E.1,E.2.trans (by norm_num [cell12984])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy11 (n := 12984) (by norm_num)
        (q := 1 - (cell12984 ⟨11,by decide⟩).lower)
        (by norm_num [cell12984]) (by norm_num [cell12984])
      exact ⟨E.1,E.2.trans (by norm_num [cell12984])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy12 (n := 12984) (by norm_num)
        (q := 1 - (cell12984 ⟨12,by decide⟩).lower)
        (by norm_num [cell12984]) (by norm_num [cell12984])
      exact ⟨E.1,E.2.trans (by norm_num [cell12984])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy13 (n := 12984) (by norm_num)
        (q := 1 - (cell12984 ⟨13,by decide⟩).lower)
        (by norm_num [cell12984]) (by norm_num [cell12984])
      exact ⟨E.1,E.2.trans (by norm_num [cell12984])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy14 (n := 12984) (by norm_num)
        (q := 1 - (cell12984 ⟨14,by decide⟩).lower)
        (by norm_num [cell12984]) (by norm_num [cell12984])
      exact ⟨E.1,E.2.trans (by norm_num [cell12984])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy15 (n := 12984) (by norm_num)
        (q := 1 - (cell12984 ⟨15,by decide⟩).lower)
        (by norm_num [cell12984]) (by norm_num [cell12984])
      exact ⟨E.1,E.2.trans (by norm_num [cell12984])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy16 (n := 12984) (by norm_num)
        (q := 1 - (cell12984 ⟨16,by decide⟩).lower)
        (by norm_num [cell12984]) (by norm_num [cell12984])
      exact ⟨E.1,E.2.trans (by norm_num [cell12984])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy17 (n := 12984) (by norm_num)
        (q := 1 - (cell12984 ⟨17,by decide⟩).lower)
        (by norm_num [cell12984]) (by norm_num [cell12984])
      exact ⟨E.1,E.2.trans (by norm_num [cell12984])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy18 (n := 12984) (by norm_num)
        (q := 1 - (cell12984 ⟨18,by decide⟩).lower)
        (by norm_num [cell12984]) (by norm_num [cell12984])
      exact ⟨E.1,E.2.trans (by norm_num [cell12984])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy19 (n := 12984) (by norm_num)
        (q := 1 - (cell12984 ⟨19,by decide⟩).lower)
        (by norm_num [cell12984]) (by norm_num [cell12984])
      exact ⟨E.1,E.2.trans (by norm_num [cell12984])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy20 (n := 12984) (by norm_num)
        (q := 1 - (cell12984 ⟨20,by decide⟩).lower)
        (by norm_num [cell12984]) (by norm_num [cell12984])
      exact ⟨E.1,E.2.trans (by norm_num [cell12984])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy21 (n := 12984) (by norm_num)
        (q := 1 - (cell12984 ⟨21,by decide⟩).lower)
        (by norm_num [cell12984]) (by norm_num [cell12984])
      exact ⟨E.1,E.2.trans (by norm_num [cell12984])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy22 (n := 12984) (by norm_num)
        (q := 1 - (cell12984 ⟨22,by decide⟩).lower)
        (by norm_num [cell12984]) (by norm_num [cell12984])
      exact ⟨E.1,E.2.trans (by norm_num [cell12984])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy23 (n := 12984) (by norm_num)
        (q := 1 - (cell12984 ⟨23,by decide⟩).lower)
        (by norm_num [cell12984]) (by norm_num [cell12984])
      exact ⟨E.1,E.2.trans (by norm_num [cell12984])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy24 (n := 12984) (by norm_num)
        (q := 1 - (cell12984 ⟨24,by decide⟩).lower)
        (by norm_num [cell12984]) (by norm_num [cell12984])
      exact ⟨E.1,E.2.trans (by norm_num [cell12984])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy25 (n := 12984) (by norm_num)
        (q := 1 - (cell12984 ⟨25,by decide⟩).lower)
        (by norm_num [cell12984]) (by norm_num [cell12984])
      exact ⟨E.1,E.2.trans (by norm_num [cell12984])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy26 (n := 12984) (by norm_num)
        (q := 1 - (cell12984 ⟨26,by decide⟩).lower)
        (by norm_num [cell12984]) (by norm_num [cell12984])
      exact ⟨E.1,E.2.trans (by norm_num [cell12984])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy27 (n := 12984) (by norm_num)
        (q := 1 - (cell12984 ⟨27,by decide⟩).lower)
        (by norm_num [cell12984]) (by norm_num [cell12984])
      exact ⟨E.1,E.2.trans (by norm_num [cell12984])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy28 (n := 12984) (by norm_num)
        (q := 1 - (cell12984 ⟨28,by decide⟩).lower)
        (by norm_num [cell12984]) (by norm_num [cell12984])
      exact ⟨E.1,E.2.trans (by norm_num [cell12984])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy29 (n := 12984) (by norm_num)
        (q := 1 - (cell12984 ⟨29,by decide⟩).lower)
        (by norm_num [cell12984]) (by norm_num [cell12984])
      exact ⟨E.1,E.2.trans (by norm_num [cell12984])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy30 (n := 12984) (by norm_num)
        (q := 1 - (cell12984 ⟨30,by decide⟩).lower)
        (by norm_num [cell12984]) (by norm_num [cell12984])
      exact ⟨E.1,E.2.trans (by norm_num [cell12984])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy31 (n := 12984) (by norm_num)
        (q := 1 - (cell12984 ⟨31,by decide⟩).lower)
        (by norm_num [cell12984]) (by norm_num [cell12984])
      exact ⟨E.1,E.2.trans (by norm_num [cell12984])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy32 (n := 12984) (by norm_num)
        (q := 1 - (cell12984 ⟨32,by decide⟩).lower)
        (by norm_num [cell12984]) (by norm_num [cell12984])
      exact ⟨E.1,E.2.trans (by norm_num [cell12984])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy33 (n := 12984) (by norm_num)
        (q := 1 - (cell12984 ⟨33,by decide⟩).lower)
        (by norm_num [cell12984]) (by norm_num [cell12984])
      exact ⟨E.1,E.2.trans (by norm_num [cell12984])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy34 (n := 12984) (by norm_num)
        (q := 1 - (cell12984 ⟨34,by decide⟩).lower)
        (by norm_num [cell12984]) (by norm_num [cell12984])
      exact ⟨E.1,E.2.trans (by norm_num [cell12984])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy35 (n := 12984) (by norm_num)
        (q := 1 - (cell12984 ⟨35,by decide⟩).lower)
        (by norm_num [cell12984]) (by norm_num [cell12984])
      exact ⟨E.1,E.2.trans (by norm_num [cell12984])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy36 (n := 12984) (by norm_num)
        (q := 1 - (cell12984 ⟨36,by decide⟩).lower)
        (by norm_num [cell12984]) (by norm_num [cell12984])
      exact ⟨E.1,E.2.trans (by norm_num [cell12984])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy37 (n := 12984) (by norm_num)
        (q := 1 - (cell12984 ⟨37,by decide⟩).lower)
        (by norm_num [cell12984]) (by norm_num [cell12984])
      exact ⟨E.1,E.2.trans (by norm_num [cell12984])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy38 (n := 12984) (by norm_num)
        (q := 1 - (cell12984 ⟨38,by decide⟩).lower)
        (by norm_num [cell12984]) (by norm_num [cell12984])
      exact ⟨E.1,E.2.trans (by norm_num [cell12984])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy39 (n := 12984) (by norm_num)
        (q := 1 - (cell12984 ⟨39,by decide⟩).lower)
        (by norm_num [cell12984]) (by norm_num [cell12984])
      exact ⟨E.1,E.2.trans (by norm_num [cell12984])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy40 (n := 12984) (by norm_num)
        (q := 1 - (cell12984 ⟨40,by decide⟩).lower)
        (by norm_num [cell12984]) (by norm_num [cell12984])
      exact ⟨E.1,E.2.trans (by norm_num [cell12984])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy41 (n := 12984) (by norm_num)
        (q := 1 - (cell12984 ⟨41,by decide⟩).lower)
        (by norm_num [cell12984]) (by norm_num [cell12984])
      exact ⟨E.1,E.2.trans (by norm_num [cell12984])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy42 (n := 12984) (by norm_num)
        (q := 1 - (cell12984 ⟨42,by decide⟩).lower)
        (by norm_num [cell12984]) (by norm_num [cell12984])
      exact ⟨E.1,E.2.trans (by norm_num [cell12984])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy43 (n := 12984) (by norm_num)
        (q := 1 - (cell12984 ⟨43,by decide⟩).lower)
        (by norm_num [cell12984]) (by norm_num [cell12984])
      exact ⟨E.1,E.2.trans (by norm_num [cell12984])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy44 (n := 12984) (by norm_num)
        (q := 1 - (cell12984 ⟨44,by decide⟩).lower)
        (by norm_num [cell12984]) (by norm_num [cell12984])
      exact ⟨E.1,E.2.trans (by norm_num [cell12984])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy45 (n := 12984) (by norm_num)
        (q := 1 - (cell12984 ⟨45,by decide⟩).lower)
        (by norm_num [cell12984]) (by norm_num [cell12984])
      exact ⟨E.1,E.2.trans (by norm_num [cell12984])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy46 (n := 12984) (by norm_num)
        (q := 1 - (cell12984 ⟨46,by decide⟩).lower)
        (by norm_num [cell12984]) (by norm_num [cell12984])
      exact ⟨E.1,E.2.trans (by norm_num [cell12984])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy47 (n := 12984) (by norm_num)
        (q := 1 - (cell12984 ⟨47,by decide⟩).lower)
        (by norm_num [cell12984]) (by norm_num [cell12984])
      exact ⟨E.1,E.2.trans (by norm_num [cell12984])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy48 (n := 12984) (by norm_num)
        (q := 1 - (cell12984 ⟨48,by decide⟩).lower)
        (by norm_num [cell12984]) (by norm_num [cell12984])
      exact ⟨E.1,E.2.trans (by norm_num [cell12984])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy49 (n := 12984) (by norm_num)
        (q := 1 - (cell12984 ⟨49,by decide⟩).lower)
        (by norm_num [cell12984]) (by norm_num [cell12984])
      exact ⟨E.1,E.2.trans (by norm_num [cell12984])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy50 (n := 12984) (by norm_num)
        (q := 1 - (cell12984 ⟨50,by decide⟩).lower)
        (by norm_num [cell12984]) (by norm_num [cell12984])
      exact ⟨E.1,E.2.trans (by norm_num [cell12984])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy51 (n := 12984) (by norm_num)
        (q := 1 - (cell12984 ⟨51,by decide⟩).lower)
        (by norm_num [cell12984]) (by norm_num [cell12984])
      exact ⟨E.1,E.2.trans (by norm_num [cell12984])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy52 (n := 12984) (by norm_num)
        (q := 1 - (cell12984 ⟨52,by decide⟩).lower)
        (by norm_num [cell12984]) (by norm_num [cell12984])
      exact ⟨E.1,E.2.trans (by norm_num [cell12984])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12984

/-! Source-cell containment and simple scalar guards at 12984. -/
namespace BstLean.Part269.N12984
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12984)
open BstLean.Part268 (cell12984)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12984 ⟨10,by decide⟩).lower ∧ (cell12984 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12984 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12984 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12984 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12984 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12984 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12984,cell12984,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12984 ⟨11,by decide⟩).lower ∧ (cell12984 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12984 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12984 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12984 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12984 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12984 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12984,cell12984,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12984 ⟨12,by decide⟩).lower ∧ (cell12984 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12984 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12984 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12984 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12984 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12984 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12984,cell12984,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12984 ⟨13,by decide⟩).lower ∧ (cell12984 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12984 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12984 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12984 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12984 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12984 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12984,cell12984,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12984 ⟨14,by decide⟩).lower ∧ (cell12984 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12984 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12984 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12984 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12984 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12984 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12984,cell12984,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12984 ⟨15,by decide⟩).lower ∧ (cell12984 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12984 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12984 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12984 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12984 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12984 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12984,cell12984,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12984 ⟨16,by decide⟩).lower ∧ (cell12984 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12984 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12984 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12984 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12984 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12984 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12984,cell12984,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12984 ⟨17,by decide⟩).lower ∧ (cell12984 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12984 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12984 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12984 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12984 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12984 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12984,cell12984,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12984 ⟨18,by decide⟩).lower ∧ (cell12984 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12984 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12984 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12984 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12984 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12984 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12984,cell12984,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12984 ⟨19,by decide⟩).lower ∧ (cell12984 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12984 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12984 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12984 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12984 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12984 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12984,cell12984,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12984 ⟨20,by decide⟩).lower ∧ (cell12984 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12984 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12984 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12984 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12984 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12984 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12984,cell12984,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12984 ⟨21,by decide⟩).lower ∧ (cell12984 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12984 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12984 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12984 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12984 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12984 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12984,cell12984,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12984 ⟨22,by decide⟩).lower ∧ (cell12984 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12984 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12984 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12984 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12984 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12984 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12984,cell12984,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12984 ⟨23,by decide⟩).lower ∧ (cell12984 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12984 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12984 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12984 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12984 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12984 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12984,cell12984,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12984 ⟨24,by decide⟩).lower ∧ (cell12984 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12984 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12984 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12984 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12984 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12984 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12984,cell12984,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12984 ⟨25,by decide⟩).lower ∧ (cell12984 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12984 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12984 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12984 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12984 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12984 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12984,cell12984,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12984 ⟨26,by decide⟩).lower ∧ (cell12984 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12984 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12984 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12984 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12984 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12984 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12984,cell12984,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12984 ⟨27,by decide⟩).lower ∧ (cell12984 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12984 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12984 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12984 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12984 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12984 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12984,cell12984,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12984 ⟨28,by decide⟩).lower ∧ (cell12984 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12984 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12984 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12984 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12984 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12984 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12984,cell12984,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12984 ⟨29,by decide⟩).lower ∧ (cell12984 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12984 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12984 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12984 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12984 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12984 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12984,cell12984,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12984 ⟨30,by decide⟩).lower ∧ (cell12984 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12984 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12984 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12984 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12984 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12984 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12984,cell12984,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12984 ⟨31,by decide⟩).lower ∧ (cell12984 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12984 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12984 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12984 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12984 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12984 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12984,cell12984,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12984 ⟨32,by decide⟩).lower ∧ (cell12984 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12984 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12984 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12984 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12984 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12984 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12984,cell12984,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12984 ⟨33,by decide⟩).lower ∧ (cell12984 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12984 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12984 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12984 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12984 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12984 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12984,cell12984,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12984 ⟨34,by decide⟩).lower ∧ (cell12984 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12984 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12984 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12984 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12984 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12984 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12984,cell12984,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12984 ⟨35,by decide⟩).lower ∧ (cell12984 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12984 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12984 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12984 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12984 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12984 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12984,cell12984,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12984 ⟨36,by decide⟩).lower ∧ (cell12984 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12984 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12984 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12984 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12984 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12984 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12984,cell12984,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12984 ⟨37,by decide⟩).lower ∧ (cell12984 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12984 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12984 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12984 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12984 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12984 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12984,cell12984,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12984 ⟨38,by decide⟩).lower ∧ (cell12984 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12984 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12984 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12984 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12984 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12984 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12984,cell12984,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12984 ⟨39,by decide⟩).lower ∧ (cell12984 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12984 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12984 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12984 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12984 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12984 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12984,cell12984,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12984 ⟨40,by decide⟩).lower ∧ (cell12984 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12984 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12984 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12984 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12984 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12984 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12984,cell12984,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12984 ⟨41,by decide⟩).lower ∧ (cell12984 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12984 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12984 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12984 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12984 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12984 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12984,cell12984,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12984 ⟨42,by decide⟩).lower ∧ (cell12984 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12984 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12984 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12984 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12984 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12984 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12984,cell12984,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12984 ⟨43,by decide⟩).lower ∧ (cell12984 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12984 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12984 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12984 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12984 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12984 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12984,cell12984,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12984 ⟨44,by decide⟩).lower ∧ (cell12984 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12984 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12984 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12984 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12984 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12984 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12984,cell12984,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12984 ⟨45,by decide⟩).lower ∧ (cell12984 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12984 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12984 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12984 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12984 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12984 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12984,cell12984,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12984 ⟨46,by decide⟩).lower ∧ (cell12984 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12984 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12984 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12984 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12984 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12984 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12984,cell12984,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12984 ⟨47,by decide⟩).lower ∧ (cell12984 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12984 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12984 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12984 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12984 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12984 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12984,cell12984,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12984 ⟨48,by decide⟩).lower ∧ (cell12984 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12984 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12984 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12984 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12984 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12984 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12984,cell12984,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12984 ⟨49,by decide⟩).lower ∧ (cell12984 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12984 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12984 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12984 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12984 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12984 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12984,cell12984,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12984 ⟨50,by decide⟩).lower ∧ (cell12984 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12984 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12984 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12984 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12984 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12984 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12984,cell12984,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12984 ⟨51,by decide⟩).lower ∧ (cell12984 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12984 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12984 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12984 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12984 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12984 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12984,cell12984,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12984 ⟨52,by decide⟩).lower ∧ (cell12984 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12984 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12984 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12984 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12984 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12984 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12984,cell12984,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12984 i).lower ∧
    (cell12984 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12984 i).upper ≤ (0.532 : ℝ) ∧
    (cell12984 i).centre ≤ (0.1 : ℝ) ∧ (cell12984 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12984 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12984 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12984

/-! The local source numeric instances at 12984 have no network premises. -/
namespace BstLean.Part269.N12984
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12984)
open BstLean.Part268 (cell12984)

noncomputable def sourceNumerics12984 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12984 (cell12984 i)
      scalarRow12984.M scalarRow12984.H scalarRow12984.xi := by
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
    energy_allowance := scalarRow12984.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12984]
    centre_nonneg := (scalarRow12984.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D25.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12984])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12984
/-! Actual 12985 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12985
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12985 ≤ (1.035410625853 : ℝ) := by
  have hr : (113.951744172697 : ℝ) ≤ √(12985 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.951744172697 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12985 12985 (11 / 1000) ≤
    (0.008388524067 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12985) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.951744172697 : ℝ) ≤ √(12985 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12985)
  have hdiv : K / √(12985 : ℝ) ≤ K / 113.951744172697 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.951744172697 ≤ (0.008388524067 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12985.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12985 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12985 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12985 := gPlus_lower 12985
end BstLean.Part269.N12985

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12985
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035410625852 : ℝ) ≤ wn 12985 := by
  have hn : √(12985 : ℝ) ≤ 113.951744172698 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12985 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.951744172698 ≤ 2 / √(12985 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000246257686 : ℝ) ≤ rhoBar 12985 BstLean.Part154.csC ∧
    rhoBar 12985 BstLean.Part154.csC ≤ 0.000246258067 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035410625852 : ℝ) / (1.295212 * 12985) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035410625853 : ℝ) / (1.29521 * 12985) := by gcongr
      _ ≤ (0.000246258067 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12985 BstLean.Part154.csC) ≤ 0.000985092912 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12985 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12985 BstLean.Part154.csC) (piBar (rhoBar 12985 BstLean.Part154.csC)) ≤ 0.000188093378 ∧
    cc1 (rhoBar 12985 BstLean.Part154.csC) (piBar (rhoBar 12985 BstLean.Part154.csC)) ≤ 0.000119685105 ∧
    cc2 (rhoBar 12985 BstLean.Part154.csC) ≤ 0.000069478169 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12985 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12985 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12985 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12985 BstLean.Part154.csC * nuR (rhoBar 12985 BstLean.Part154.csC)) ≤ 0.000492531295 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000246258067 : ℝ) * 0.000985092912 := by gcongr
      _ ≤ (0.000492531295 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12985 BstLean.Part154.csC) * nuR (rhoBar 12985 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000985092912 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12985 BstLean.Part154.csC) * rhoBar 12985 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000246258067 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000246258067 / 2 + 0.399 * 0.000985092912 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000188093378 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000492531295 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119685105 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000246258067 / 1.414213562 := by gcongr
      _ ≤ (0.000069478169 : ℝ) := by norm_num

end BstLean.Part269.N12985

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12985
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12985 BstLean.Part154.csC) (piBar (rhoBar 12985 BstLean.Part154.csC)) ≤ 1.52786E-7 := by
  have hr0 : 0 ≤ rhoBar 12985 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12985 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12985 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12985 BstLean.Part154.csC) (piBar (rhoBar 12985 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12985 BstLean.Part154.csC) (piBar (rhoBar 12985 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12985 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000188093378 : ℝ) ^ 2 + 0.000119685105 ^ 2 + 3 * 0.000069478169 ^ 2 +
        2 * 0.797885 * 0.000188093378 * 0.000119685105 + 2 * 0.000188093378 * 0.000069478169 +
        4 * 0.797885 * 0.000119685105 * 0.000069478169 := by gcongr
    _ ≤ (1.52786E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12985 BstLean.Part154.csC Θ ≤ 0.002569605042 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12985 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12985 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12985 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12985 BstLean.Part154.csC) (piBar (rhoBar 12985 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12985 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035410625853 * 1.52786E-7 / (0.000246257686 : ℝ) := by gcongr
    _ ≤ 0.002569605042 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12985 BstLean.Part154.csC Θ ≤ 0.002850010368 + 0.000649296839 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12985 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12985 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12985 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035410625853 : ℝ) * ((2 * Θ * 0.000246258067 +
        (6863 / 10000) * 0.000246258067 * 12985 * 0.000985092912) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002850010368 + 0.000649296839 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12985 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12985 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12985 0.011 Θ ∧ gammaRatio 12985 0.011 Θ ≤ 0.000084657156 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12985 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035410625853 : ℝ) * 0.525 / ((1 - 0.011) * 12985) := by gcongr
      _ ≤ (0.000084657156 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12985 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12985 0.011 Θ) :=
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
    badAllowance 12985 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000421835223 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12985 BstLean.Part154.csC) 1.22 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 2 (rhoBar 12985 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12985 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12985 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12985 0.011 Θ) 1.12 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 1 (gammaRatio 12985 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12985 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12985 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12985 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12985 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035410625853 : ℝ) * 12985 *
        (1.5230E-8 / 1.1045361 + 1.8602E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000421835223 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12985 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003271845591 + 0.003218901881 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12985

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12985
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12985 BstLean.Part154.csC) (piBar (rhoBar 12985 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12985 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12985 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12985 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12985 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12985 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12985 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12985 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12985 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12985 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12985 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12985 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12985 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12985 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12985 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051898932914 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12985) ≤ 0.010480204492 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12985 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035410625853)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010480204492 + 2 * 0.737676 / 12985) := by gcongr
    _ ≤ (0.051898932914 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12985 12 ≤ 0.0015 := by
  exact BstLean.Part269.S25.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12985

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12985
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560516173954 : ℝ) ≤ plow 12985 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12985) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052468369079)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001349042648) : eMP 12985 0.011 xi bn ≤ 0.001161778898 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12985 : ℝ) * (1 - 0.011))) ≤ 0.000574471751 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001349042648 / (12985 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000574471751 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000574471751 : ℝ) + 3.141593 * 0.052468369079 / (12985 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001161778898 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052468369079)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001349042648) : PiBarMP 12985 12 0.011 xi bn ≤ 0.159454053603 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12985 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036729315921 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.323276514580 : ℝ) ≤ √((12985 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.951744172697 : ℝ) ≤ √(12985 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12985) ≤ 0.122265862308 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036729315921 + 0.052468369079 * 1.772454 / (2 * (113.323276514580 : ℝ))) * (1 + 0.001161778898) +
        8 / (12985 * 113.951744172697) + 0.122265862308 := by gcongr
    _ ≤ (0.159454053603 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052468369079)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001349042648) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280958682934) :
    parallelOracle 12985 0.011 xi bn cd ≤ 0.160422695405 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12985 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12985 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560516173954 : ℝ) ≤ plow 12985 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.951744172697 : ℝ) ≤ √(12985 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280958682934 : ℝ) / (2 * 0.560516173954 * 113.951744172697)) * 0.159454053603 +
        0.280958682934 ^ 2 / (2 * 0.560516173954 * 113.951744172697) := by gcongr
    _ ≤ (0.160422695405 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052468369079) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001349042648)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280958682934) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12985 12985 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560516173954 : ℝ) ≤ plow 12985 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.951744172697 : ℝ) ≤ √(12985 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12985 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12985 Θ 1.22 ≤ 0.011637386595 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.951744172697 := by gcongr <;> linarith
      _ ≤ (0.011637386595 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12985 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12985 12985 0.011 ≤ 0.008388524067 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12985 12985 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12985 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12985 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12985 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12985 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160422695405 + 0.011637386595 + (0.008388524067 : ℝ) *
        (1 + 2 * (0.280958682934 + 0.011637386595) / (0.560516173954 * 113.951744172697))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12985]

end BstLean.Part269.N12985

/-! The original eight local profiles supply actual 12985 moment certificates. -/
namespace BstLean.Part269.N12985
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12985 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12985 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12985 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052468369079 ∧
    0 ≤ bN 12985 BstLean.Part154.csC (groupTheta g) ∧ bN 12985 BstLean.Part154.csC (groupTheta g) ≤ 0.001349042648 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12985 12985 0.011
      (momentAllowance 12985 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12985 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12985 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12985 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12985 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12985 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229059750020 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12985 0.011
      (momentAllowance 12985 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12985 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12985
/-! The actual computed-centre upper energy formula at 12985. -/
namespace BstLean.Part269.N12985
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12985

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12985
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12985)
open BstLean.Part268 (cell12985)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084699485337
  | 2 => 0.085628680319
  | 3 => 0.086554164005
  | 4 => 0.087476919371
  | 5 => 0.088398148210
  | 6 => 0.089319305232
  | 7 => 0.090242135672
  | 8 => 0.091168716504
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12985 12985 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12985 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003274156000 + 0.003221457154 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S25.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12985

/-! Actual upper energy certificates on all 43 source endpoints at 12985. -/
namespace BstLean.Part269.N12985
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12985)
open BstLean.Part268 (cell12985)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12985 (gMinus 12985) (1 - (cell12985 i).lower) ≤ 1 ∧
    energyUpper 12985 (gMinus 12985) (BstLean.Part211.gPlus 12985)
      (finiteEnergy 12985 12985 0.011) (1 - (cell12985 i).lower) ≤
      (cell12985 i).energy := by
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
      have E := BstLean.Part269.S25.uniformEnergy10 (n := 12985) (by norm_num)
        (q := 1 - (cell12985 ⟨10,by decide⟩).lower)
        (by norm_num [cell12985]) (by norm_num [cell12985])
      exact ⟨E.1,E.2.trans (by norm_num [cell12985])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy11 (n := 12985) (by norm_num)
        (q := 1 - (cell12985 ⟨11,by decide⟩).lower)
        (by norm_num [cell12985]) (by norm_num [cell12985])
      exact ⟨E.1,E.2.trans (by norm_num [cell12985])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy12 (n := 12985) (by norm_num)
        (q := 1 - (cell12985 ⟨12,by decide⟩).lower)
        (by norm_num [cell12985]) (by norm_num [cell12985])
      exact ⟨E.1,E.2.trans (by norm_num [cell12985])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy13 (n := 12985) (by norm_num)
        (q := 1 - (cell12985 ⟨13,by decide⟩).lower)
        (by norm_num [cell12985]) (by norm_num [cell12985])
      exact ⟨E.1,E.2.trans (by norm_num [cell12985])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy14 (n := 12985) (by norm_num)
        (q := 1 - (cell12985 ⟨14,by decide⟩).lower)
        (by norm_num [cell12985]) (by norm_num [cell12985])
      exact ⟨E.1,E.2.trans (by norm_num [cell12985])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy15 (n := 12985) (by norm_num)
        (q := 1 - (cell12985 ⟨15,by decide⟩).lower)
        (by norm_num [cell12985]) (by norm_num [cell12985])
      exact ⟨E.1,E.2.trans (by norm_num [cell12985])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy16 (n := 12985) (by norm_num)
        (q := 1 - (cell12985 ⟨16,by decide⟩).lower)
        (by norm_num [cell12985]) (by norm_num [cell12985])
      exact ⟨E.1,E.2.trans (by norm_num [cell12985])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy17 (n := 12985) (by norm_num)
        (q := 1 - (cell12985 ⟨17,by decide⟩).lower)
        (by norm_num [cell12985]) (by norm_num [cell12985])
      exact ⟨E.1,E.2.trans (by norm_num [cell12985])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy18 (n := 12985) (by norm_num)
        (q := 1 - (cell12985 ⟨18,by decide⟩).lower)
        (by norm_num [cell12985]) (by norm_num [cell12985])
      exact ⟨E.1,E.2.trans (by norm_num [cell12985])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy19 (n := 12985) (by norm_num)
        (q := 1 - (cell12985 ⟨19,by decide⟩).lower)
        (by norm_num [cell12985]) (by norm_num [cell12985])
      exact ⟨E.1,E.2.trans (by norm_num [cell12985])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy20 (n := 12985) (by norm_num)
        (q := 1 - (cell12985 ⟨20,by decide⟩).lower)
        (by norm_num [cell12985]) (by norm_num [cell12985])
      exact ⟨E.1,E.2.trans (by norm_num [cell12985])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy21 (n := 12985) (by norm_num)
        (q := 1 - (cell12985 ⟨21,by decide⟩).lower)
        (by norm_num [cell12985]) (by norm_num [cell12985])
      exact ⟨E.1,E.2.trans (by norm_num [cell12985])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy22 (n := 12985) (by norm_num)
        (q := 1 - (cell12985 ⟨22,by decide⟩).lower)
        (by norm_num [cell12985]) (by norm_num [cell12985])
      exact ⟨E.1,E.2.trans (by norm_num [cell12985])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy23 (n := 12985) (by norm_num)
        (q := 1 - (cell12985 ⟨23,by decide⟩).lower)
        (by norm_num [cell12985]) (by norm_num [cell12985])
      exact ⟨E.1,E.2.trans (by norm_num [cell12985])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy24 (n := 12985) (by norm_num)
        (q := 1 - (cell12985 ⟨24,by decide⟩).lower)
        (by norm_num [cell12985]) (by norm_num [cell12985])
      exact ⟨E.1,E.2.trans (by norm_num [cell12985])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy25 (n := 12985) (by norm_num)
        (q := 1 - (cell12985 ⟨25,by decide⟩).lower)
        (by norm_num [cell12985]) (by norm_num [cell12985])
      exact ⟨E.1,E.2.trans (by norm_num [cell12985])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy26 (n := 12985) (by norm_num)
        (q := 1 - (cell12985 ⟨26,by decide⟩).lower)
        (by norm_num [cell12985]) (by norm_num [cell12985])
      exact ⟨E.1,E.2.trans (by norm_num [cell12985])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy27 (n := 12985) (by norm_num)
        (q := 1 - (cell12985 ⟨27,by decide⟩).lower)
        (by norm_num [cell12985]) (by norm_num [cell12985])
      exact ⟨E.1,E.2.trans (by norm_num [cell12985])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy28 (n := 12985) (by norm_num)
        (q := 1 - (cell12985 ⟨28,by decide⟩).lower)
        (by norm_num [cell12985]) (by norm_num [cell12985])
      exact ⟨E.1,E.2.trans (by norm_num [cell12985])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy29 (n := 12985) (by norm_num)
        (q := 1 - (cell12985 ⟨29,by decide⟩).lower)
        (by norm_num [cell12985]) (by norm_num [cell12985])
      exact ⟨E.1,E.2.trans (by norm_num [cell12985])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy30 (n := 12985) (by norm_num)
        (q := 1 - (cell12985 ⟨30,by decide⟩).lower)
        (by norm_num [cell12985]) (by norm_num [cell12985])
      exact ⟨E.1,E.2.trans (by norm_num [cell12985])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy31 (n := 12985) (by norm_num)
        (q := 1 - (cell12985 ⟨31,by decide⟩).lower)
        (by norm_num [cell12985]) (by norm_num [cell12985])
      exact ⟨E.1,E.2.trans (by norm_num [cell12985])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy32 (n := 12985) (by norm_num)
        (q := 1 - (cell12985 ⟨32,by decide⟩).lower)
        (by norm_num [cell12985]) (by norm_num [cell12985])
      exact ⟨E.1,E.2.trans (by norm_num [cell12985])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy33 (n := 12985) (by norm_num)
        (q := 1 - (cell12985 ⟨33,by decide⟩).lower)
        (by norm_num [cell12985]) (by norm_num [cell12985])
      exact ⟨E.1,E.2.trans (by norm_num [cell12985])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy34 (n := 12985) (by norm_num)
        (q := 1 - (cell12985 ⟨34,by decide⟩).lower)
        (by norm_num [cell12985]) (by norm_num [cell12985])
      exact ⟨E.1,E.2.trans (by norm_num [cell12985])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy35 (n := 12985) (by norm_num)
        (q := 1 - (cell12985 ⟨35,by decide⟩).lower)
        (by norm_num [cell12985]) (by norm_num [cell12985])
      exact ⟨E.1,E.2.trans (by norm_num [cell12985])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy36 (n := 12985) (by norm_num)
        (q := 1 - (cell12985 ⟨36,by decide⟩).lower)
        (by norm_num [cell12985]) (by norm_num [cell12985])
      exact ⟨E.1,E.2.trans (by norm_num [cell12985])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy37 (n := 12985) (by norm_num)
        (q := 1 - (cell12985 ⟨37,by decide⟩).lower)
        (by norm_num [cell12985]) (by norm_num [cell12985])
      exact ⟨E.1,E.2.trans (by norm_num [cell12985])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy38 (n := 12985) (by norm_num)
        (q := 1 - (cell12985 ⟨38,by decide⟩).lower)
        (by norm_num [cell12985]) (by norm_num [cell12985])
      exact ⟨E.1,E.2.trans (by norm_num [cell12985])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy39 (n := 12985) (by norm_num)
        (q := 1 - (cell12985 ⟨39,by decide⟩).lower)
        (by norm_num [cell12985]) (by norm_num [cell12985])
      exact ⟨E.1,E.2.trans (by norm_num [cell12985])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy40 (n := 12985) (by norm_num)
        (q := 1 - (cell12985 ⟨40,by decide⟩).lower)
        (by norm_num [cell12985]) (by norm_num [cell12985])
      exact ⟨E.1,E.2.trans (by norm_num [cell12985])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy41 (n := 12985) (by norm_num)
        (q := 1 - (cell12985 ⟨41,by decide⟩).lower)
        (by norm_num [cell12985]) (by norm_num [cell12985])
      exact ⟨E.1,E.2.trans (by norm_num [cell12985])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy42 (n := 12985) (by norm_num)
        (q := 1 - (cell12985 ⟨42,by decide⟩).lower)
        (by norm_num [cell12985]) (by norm_num [cell12985])
      exact ⟨E.1,E.2.trans (by norm_num [cell12985])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy43 (n := 12985) (by norm_num)
        (q := 1 - (cell12985 ⟨43,by decide⟩).lower)
        (by norm_num [cell12985]) (by norm_num [cell12985])
      exact ⟨E.1,E.2.trans (by norm_num [cell12985])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy44 (n := 12985) (by norm_num)
        (q := 1 - (cell12985 ⟨44,by decide⟩).lower)
        (by norm_num [cell12985]) (by norm_num [cell12985])
      exact ⟨E.1,E.2.trans (by norm_num [cell12985])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy45 (n := 12985) (by norm_num)
        (q := 1 - (cell12985 ⟨45,by decide⟩).lower)
        (by norm_num [cell12985]) (by norm_num [cell12985])
      exact ⟨E.1,E.2.trans (by norm_num [cell12985])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy46 (n := 12985) (by norm_num)
        (q := 1 - (cell12985 ⟨46,by decide⟩).lower)
        (by norm_num [cell12985]) (by norm_num [cell12985])
      exact ⟨E.1,E.2.trans (by norm_num [cell12985])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy47 (n := 12985) (by norm_num)
        (q := 1 - (cell12985 ⟨47,by decide⟩).lower)
        (by norm_num [cell12985]) (by norm_num [cell12985])
      exact ⟨E.1,E.2.trans (by norm_num [cell12985])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy48 (n := 12985) (by norm_num)
        (q := 1 - (cell12985 ⟨48,by decide⟩).lower)
        (by norm_num [cell12985]) (by norm_num [cell12985])
      exact ⟨E.1,E.2.trans (by norm_num [cell12985])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy49 (n := 12985) (by norm_num)
        (q := 1 - (cell12985 ⟨49,by decide⟩).lower)
        (by norm_num [cell12985]) (by norm_num [cell12985])
      exact ⟨E.1,E.2.trans (by norm_num [cell12985])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy50 (n := 12985) (by norm_num)
        (q := 1 - (cell12985 ⟨50,by decide⟩).lower)
        (by norm_num [cell12985]) (by norm_num [cell12985])
      exact ⟨E.1,E.2.trans (by norm_num [cell12985])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy51 (n := 12985) (by norm_num)
        (q := 1 - (cell12985 ⟨51,by decide⟩).lower)
        (by norm_num [cell12985]) (by norm_num [cell12985])
      exact ⟨E.1,E.2.trans (by norm_num [cell12985])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy52 (n := 12985) (by norm_num)
        (q := 1 - (cell12985 ⟨52,by decide⟩).lower)
        (by norm_num [cell12985]) (by norm_num [cell12985])
      exact ⟨E.1,E.2.trans (by norm_num [cell12985])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12985

/-! Source-cell containment and simple scalar guards at 12985. -/
namespace BstLean.Part269.N12985
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12985)
open BstLean.Part268 (cell12985)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12985 ⟨10,by decide⟩).lower ∧ (cell12985 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12985 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12985 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12985 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12985 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12985 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12985,cell12985,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12985 ⟨11,by decide⟩).lower ∧ (cell12985 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12985 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12985 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12985 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12985 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12985 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12985,cell12985,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12985 ⟨12,by decide⟩).lower ∧ (cell12985 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12985 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12985 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12985 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12985 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12985 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12985,cell12985,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12985 ⟨13,by decide⟩).lower ∧ (cell12985 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12985 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12985 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12985 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12985 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12985 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12985,cell12985,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12985 ⟨14,by decide⟩).lower ∧ (cell12985 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12985 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12985 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12985 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12985 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12985 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12985,cell12985,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12985 ⟨15,by decide⟩).lower ∧ (cell12985 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12985 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12985 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12985 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12985 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12985 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12985,cell12985,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12985 ⟨16,by decide⟩).lower ∧ (cell12985 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12985 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12985 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12985 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12985 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12985 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12985,cell12985,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12985 ⟨17,by decide⟩).lower ∧ (cell12985 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12985 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12985 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12985 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12985 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12985 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12985,cell12985,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12985 ⟨18,by decide⟩).lower ∧ (cell12985 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12985 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12985 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12985 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12985 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12985 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12985,cell12985,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12985 ⟨19,by decide⟩).lower ∧ (cell12985 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12985 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12985 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12985 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12985 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12985 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12985,cell12985,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12985 ⟨20,by decide⟩).lower ∧ (cell12985 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12985 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12985 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12985 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12985 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12985 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12985,cell12985,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12985 ⟨21,by decide⟩).lower ∧ (cell12985 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12985 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12985 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12985 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12985 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12985 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12985,cell12985,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12985 ⟨22,by decide⟩).lower ∧ (cell12985 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12985 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12985 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12985 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12985 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12985 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12985,cell12985,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12985 ⟨23,by decide⟩).lower ∧ (cell12985 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12985 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12985 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12985 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12985 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12985 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12985,cell12985,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12985 ⟨24,by decide⟩).lower ∧ (cell12985 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12985 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12985 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12985 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12985 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12985 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12985,cell12985,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12985 ⟨25,by decide⟩).lower ∧ (cell12985 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12985 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12985 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12985 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12985 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12985 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12985,cell12985,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12985 ⟨26,by decide⟩).lower ∧ (cell12985 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12985 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12985 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12985 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12985 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12985 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12985,cell12985,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12985 ⟨27,by decide⟩).lower ∧ (cell12985 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12985 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12985 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12985 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12985 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12985 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12985,cell12985,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12985 ⟨28,by decide⟩).lower ∧ (cell12985 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12985 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12985 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12985 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12985 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12985 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12985,cell12985,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12985 ⟨29,by decide⟩).lower ∧ (cell12985 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12985 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12985 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12985 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12985 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12985 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12985,cell12985,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12985 ⟨30,by decide⟩).lower ∧ (cell12985 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12985 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12985 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12985 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12985 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12985 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12985,cell12985,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12985 ⟨31,by decide⟩).lower ∧ (cell12985 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12985 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12985 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12985 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12985 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12985 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12985,cell12985,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12985 ⟨32,by decide⟩).lower ∧ (cell12985 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12985 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12985 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12985 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12985 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12985 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12985,cell12985,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12985 ⟨33,by decide⟩).lower ∧ (cell12985 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12985 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12985 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12985 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12985 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12985 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12985,cell12985,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12985 ⟨34,by decide⟩).lower ∧ (cell12985 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12985 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12985 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12985 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12985 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12985 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12985,cell12985,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12985 ⟨35,by decide⟩).lower ∧ (cell12985 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12985 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12985 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12985 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12985 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12985 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12985,cell12985,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12985 ⟨36,by decide⟩).lower ∧ (cell12985 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12985 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12985 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12985 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12985 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12985 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12985,cell12985,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12985 ⟨37,by decide⟩).lower ∧ (cell12985 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12985 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12985 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12985 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12985 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12985 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12985,cell12985,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12985 ⟨38,by decide⟩).lower ∧ (cell12985 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12985 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12985 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12985 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12985 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12985 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12985,cell12985,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12985 ⟨39,by decide⟩).lower ∧ (cell12985 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12985 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12985 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12985 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12985 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12985 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12985,cell12985,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12985 ⟨40,by decide⟩).lower ∧ (cell12985 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12985 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12985 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12985 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12985 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12985 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12985,cell12985,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12985 ⟨41,by decide⟩).lower ∧ (cell12985 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12985 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12985 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12985 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12985 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12985 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12985,cell12985,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12985 ⟨42,by decide⟩).lower ∧ (cell12985 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12985 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12985 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12985 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12985 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12985 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12985,cell12985,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12985 ⟨43,by decide⟩).lower ∧ (cell12985 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12985 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12985 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12985 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12985 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12985 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12985,cell12985,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12985 ⟨44,by decide⟩).lower ∧ (cell12985 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12985 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12985 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12985 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12985 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12985 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12985,cell12985,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12985 ⟨45,by decide⟩).lower ∧ (cell12985 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12985 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12985 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12985 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12985 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12985 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12985,cell12985,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12985 ⟨46,by decide⟩).lower ∧ (cell12985 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12985 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12985 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12985 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12985 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12985 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12985,cell12985,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12985 ⟨47,by decide⟩).lower ∧ (cell12985 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12985 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12985 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12985 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12985 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12985 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12985,cell12985,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12985 ⟨48,by decide⟩).lower ∧ (cell12985 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12985 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12985 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12985 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12985 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12985 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12985,cell12985,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12985 ⟨49,by decide⟩).lower ∧ (cell12985 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12985 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12985 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12985 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12985 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12985 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12985,cell12985,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12985 ⟨50,by decide⟩).lower ∧ (cell12985 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12985 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12985 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12985 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12985 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12985 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12985,cell12985,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12985 ⟨51,by decide⟩).lower ∧ (cell12985 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12985 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12985 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12985 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12985 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12985 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12985,cell12985,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12985 ⟨52,by decide⟩).lower ∧ (cell12985 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12985 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12985 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12985 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12985 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12985 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12985,cell12985,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12985 i).lower ∧
    (cell12985 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12985 i).upper ≤ (0.532 : ℝ) ∧
    (cell12985 i).centre ≤ (0.1 : ℝ) ∧ (cell12985 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12985 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12985 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12985

/-! The local source numeric instances at 12985 have no network premises. -/
namespace BstLean.Part269.N12985
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12985)
open BstLean.Part268 (cell12985)

noncomputable def sourceNumerics12985 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12985 (cell12985 i)
      scalarRow12985.M scalarRow12985.H scalarRow12985.xi := by
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
    energy_allowance := scalarRow12985.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12985]
    centre_nonneg := (scalarRow12985.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D25.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12985])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12985
/-! Actual 12986 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12986
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12986 ≤ (1.035409250550 : ℝ) := by
  have hr : (113.956131910485 : ℝ) ≤ √(12986 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.956131910485 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12986 12986 (11 / 1000) ≤
    (0.008388201075 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12986) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.956131910485 : ℝ) ≤ √(12986 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12986)
  have hdiv : K / √(12986 : ℝ) ≤ K / 113.956131910485 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.956131910485 ≤ (0.008388201075 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12986.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12986 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12986 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12986 := gPlus_lower 12986
end BstLean.Part269.N12986

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12986
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035409250549 : ℝ) ≤ wn 12986 := by
  have hn : √(12986 : ℝ) ≤ 113.956131910486 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12986 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.956131910486 ≤ 2 / √(12986 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000246238396 : ℝ) ≤ rhoBar 12986 BstLean.Part154.csC ∧
    rhoBar 12986 BstLean.Part154.csC ≤ 0.000246238777 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035409250549 : ℝ) / (1.295212 * 12986) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035409250550 : ℝ) / (1.29521 * 12986) := by gcongr
      _ ≤ (0.000246238777 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12986 BstLean.Part154.csC) ≤ 0.000985015742 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12986 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12986 BstLean.Part154.csC) (piBar (rhoBar 12986 BstLean.Part154.csC)) ≤ 0.000188078643 ∧
    cc1 (rhoBar 12986 BstLean.Part154.csC) (piBar (rhoBar 12986 BstLean.Part154.csC)) ≤ 0.000119675730 ∧
    cc2 (rhoBar 12986 BstLean.Part154.csC) ≤ 0.000069472727 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12986 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12986 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12986 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12986 BstLean.Part154.csC * nuR (rhoBar 12986 BstLean.Part154.csC)) ≤ 0.000492492713 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000246238777 : ℝ) * 0.000985015742 := by gcongr
      _ ≤ (0.000492492713 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12986 BstLean.Part154.csC) * nuR (rhoBar 12986 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000985015742 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12986 BstLean.Part154.csC) * rhoBar 12986 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000246238777 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000246238777 / 2 + 0.399 * 0.000985015742 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000188078643 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000492492713 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119675730 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000246238777 / 1.414213562 := by gcongr
      _ ≤ (0.000069472727 : ℝ) := by norm_num

end BstLean.Part269.N12986

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12986
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12986 BstLean.Part154.csC) (piBar (rhoBar 12986 BstLean.Part154.csC)) ≤ 1.52762E-7 := by
  have hr0 : 0 ≤ rhoBar 12986 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12986 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12986 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12986 BstLean.Part154.csC) (piBar (rhoBar 12986 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12986 BstLean.Part154.csC) (piBar (rhoBar 12986 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12986 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000188078643 : ℝ) ^ 2 + 0.000119675730 ^ 2 + 3 * 0.000069472727 ^ 2 +
        2 * 0.797885 * 0.000188078643 * 0.000119675730 + 2 * 0.000188078643 * 0.000069472727 +
        4 * 0.797885 * 0.000119675730 * 0.000069472727 := by gcongr
    _ ≤ (1.52762E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12986 BstLean.Part154.csC Θ ≤ 0.002569399258 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12986 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12986 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12986 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12986 BstLean.Part154.csC) (piBar (rhoBar 12986 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12986 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035409250550 * 1.52762E-7 / (0.000246238396 : ℝ) := by gcongr
    _ ≤ 0.002569399258 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12986 BstLean.Part154.csC Θ ≤ 0.002849779539 + 0.000649245116 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12986 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12986 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12986 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035409250550 : ℝ) * ((2 * Θ * 0.000246238777 +
        (6863 / 10000) * 0.000246238777 * 12986 * 0.000985015742) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002849779539 + 0.000649245116 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12986 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12986 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12986 0.011 Θ ∧ gammaRatio 12986 0.011 Θ ≤ 0.000084650524 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12986 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035409250550 : ℝ) * 0.525 / ((1 - 0.011) * 12986) := by gcongr
      _ ≤ (0.000084650524 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12986 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12986 0.011 Θ) :=
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
    badAllowance 12986 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000421835223 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12986 BstLean.Part154.csC) 1.22 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 2 (rhoBar 12986 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12986 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12986 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12986 0.011 Θ) 1.12 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 1 (gammaRatio 12986 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12986 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12986 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12986 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12986 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035409250550 : ℝ) * 12986 *
        (1.5230E-8 / 1.1045361 + 1.8602E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000421835223 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12986 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003271614762 + 0.003218644374 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12986

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12986
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12986 BstLean.Part154.csC) (piBar (rhoBar 12986 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12986 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12986 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12986 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12986 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12986 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12986 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12986 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12986 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12986 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12986 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12986 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12986 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12986 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12986 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051896913181 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12986) ≤ 0.010479800965 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12986 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035409250550)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010479800965 + 2 * 0.737676 / 12986) := by gcongr
    _ ≤ (0.051896913181 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12986 12 ≤ 0.0015 := by
  exact BstLean.Part269.S25.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12986

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12986
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560516217210 : ℝ) ≤ plow 12986 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12986) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052468003059)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001348934611) : eMP 12986 0.011 xi bn ≤ 0.001161687576 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12986 : ℝ) * (1 - 0.011))) ≤ 0.000574426629 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001348934611 / (12986 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000574426629 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000574426629 : ℝ) + 3.141593 * 0.052468003059 / (12986 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001161687576 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052468003059)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001348934611) : PiBarMP 12986 12 0.011 xi bn ≤ 0.159447850755 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12986 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036727845173 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.327640053077 : ℝ) ≤ √((12986 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.956131910485 : ℝ) ≤ √(12986 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12986) ≤ 0.122261154615 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036727845173 + 0.052468003059 * 1.772454 / (2 * (113.327640053077 : ℝ))) * (1 + 0.001161687576) +
        8 / (12986 * 113.956131910485) + 0.122261154615 := by gcongr
    _ ≤ (0.159447850755 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052468003059)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001348934611) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280955864238) :
    parallelOracle 12986 0.011 xi bn cd ≤ 0.160416425627 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12986 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12986 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560516217210 : ℝ) ≤ plow 12986 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.956131910485 : ℝ) ≤ √(12986 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280955864238 : ℝ) / (2 * 0.560516217210 * 113.956131910485)) * 0.159447850755 +
        0.280955864238 ^ 2 / (2 * 0.560516217210 * 113.956131910485) := by gcongr
    _ ≤ (0.160416425627 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052468003059) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001348934611)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280955864238) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12986 12986 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560516217210 : ℝ) ≤ plow 12986 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.956131910485 : ℝ) ≤ √(12986 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12986 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12986 Θ 1.22 ≤ 0.011636938512 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.956131910485 := by gcongr <;> linarith
      _ ≤ (0.011636938512 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12986 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12986 12986 0.011 ≤ 0.008388201075 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12986 12986 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12986 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12986 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12986 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12986 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160416425627 + 0.011636938512 + (0.008388201075 : ℝ) *
        (1 + 2 * (0.280955864238 + 0.011636938512) / (0.560516217210 * 113.956131910485))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12986]

end BstLean.Part269.N12986

/-! The original eight local profiles supply actual 12986 moment certificates. -/
namespace BstLean.Part269.N12986
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12986 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12986 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12986 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052468003059 ∧
    0 ≤ bN 12986 BstLean.Part154.csC (groupTheta g) ∧ bN 12986 BstLean.Part154.csC (groupTheta g) ≤ 0.001348934611 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12986 12986 0.011
      (momentAllowance 12986 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12986 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12986 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12986 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12986 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12986 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229058951057 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12986 0.011
      (momentAllowance 12986 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12986 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12986
/-! The actual computed-centre upper energy formula at 12986. -/
namespace BstLean.Part269.N12986
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12986

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12986
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12986)
open BstLean.Part268 (cell12986)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084696854934
  | 2 => 0.085626014937
  | 3 => 0.086551458283
  | 4 => 0.087474166696
  | 5 => 0.088395340491
  | 6 => 0.089316432640
  | 7 => 0.090239186350
  | 8 => 0.091165676247
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12986 12986 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12986 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003274156000 + 0.003221457154 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S25.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12986

/-! Actual upper energy certificates on all 43 source endpoints at 12986. -/
namespace BstLean.Part269.N12986
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12986)
open BstLean.Part268 (cell12986)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12986 (gMinus 12986) (1 - (cell12986 i).lower) ≤ 1 ∧
    energyUpper 12986 (gMinus 12986) (BstLean.Part211.gPlus 12986)
      (finiteEnergy 12986 12986 0.011) (1 - (cell12986 i).lower) ≤
      (cell12986 i).energy := by
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
      have E := BstLean.Part269.S25.uniformEnergy10 (n := 12986) (by norm_num)
        (q := 1 - (cell12986 ⟨10,by decide⟩).lower)
        (by norm_num [cell12986]) (by norm_num [cell12986])
      exact ⟨E.1,E.2.trans (by norm_num [cell12986])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy11 (n := 12986) (by norm_num)
        (q := 1 - (cell12986 ⟨11,by decide⟩).lower)
        (by norm_num [cell12986]) (by norm_num [cell12986])
      exact ⟨E.1,E.2.trans (by norm_num [cell12986])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy12 (n := 12986) (by norm_num)
        (q := 1 - (cell12986 ⟨12,by decide⟩).lower)
        (by norm_num [cell12986]) (by norm_num [cell12986])
      exact ⟨E.1,E.2.trans (by norm_num [cell12986])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy13 (n := 12986) (by norm_num)
        (q := 1 - (cell12986 ⟨13,by decide⟩).lower)
        (by norm_num [cell12986]) (by norm_num [cell12986])
      exact ⟨E.1,E.2.trans (by norm_num [cell12986])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy14 (n := 12986) (by norm_num)
        (q := 1 - (cell12986 ⟨14,by decide⟩).lower)
        (by norm_num [cell12986]) (by norm_num [cell12986])
      exact ⟨E.1,E.2.trans (by norm_num [cell12986])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy15 (n := 12986) (by norm_num)
        (q := 1 - (cell12986 ⟨15,by decide⟩).lower)
        (by norm_num [cell12986]) (by norm_num [cell12986])
      exact ⟨E.1,E.2.trans (by norm_num [cell12986])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy16 (n := 12986) (by norm_num)
        (q := 1 - (cell12986 ⟨16,by decide⟩).lower)
        (by norm_num [cell12986]) (by norm_num [cell12986])
      exact ⟨E.1,E.2.trans (by norm_num [cell12986])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy17 (n := 12986) (by norm_num)
        (q := 1 - (cell12986 ⟨17,by decide⟩).lower)
        (by norm_num [cell12986]) (by norm_num [cell12986])
      exact ⟨E.1,E.2.trans (by norm_num [cell12986])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy18 (n := 12986) (by norm_num)
        (q := 1 - (cell12986 ⟨18,by decide⟩).lower)
        (by norm_num [cell12986]) (by norm_num [cell12986])
      exact ⟨E.1,E.2.trans (by norm_num [cell12986])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy19 (n := 12986) (by norm_num)
        (q := 1 - (cell12986 ⟨19,by decide⟩).lower)
        (by norm_num [cell12986]) (by norm_num [cell12986])
      exact ⟨E.1,E.2.trans (by norm_num [cell12986])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy20 (n := 12986) (by norm_num)
        (q := 1 - (cell12986 ⟨20,by decide⟩).lower)
        (by norm_num [cell12986]) (by norm_num [cell12986])
      exact ⟨E.1,E.2.trans (by norm_num [cell12986])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy21 (n := 12986) (by norm_num)
        (q := 1 - (cell12986 ⟨21,by decide⟩).lower)
        (by norm_num [cell12986]) (by norm_num [cell12986])
      exact ⟨E.1,E.2.trans (by norm_num [cell12986])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy22 (n := 12986) (by norm_num)
        (q := 1 - (cell12986 ⟨22,by decide⟩).lower)
        (by norm_num [cell12986]) (by norm_num [cell12986])
      exact ⟨E.1,E.2.trans (by norm_num [cell12986])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy23 (n := 12986) (by norm_num)
        (q := 1 - (cell12986 ⟨23,by decide⟩).lower)
        (by norm_num [cell12986]) (by norm_num [cell12986])
      exact ⟨E.1,E.2.trans (by norm_num [cell12986])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy24 (n := 12986) (by norm_num)
        (q := 1 - (cell12986 ⟨24,by decide⟩).lower)
        (by norm_num [cell12986]) (by norm_num [cell12986])
      exact ⟨E.1,E.2.trans (by norm_num [cell12986])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy25 (n := 12986) (by norm_num)
        (q := 1 - (cell12986 ⟨25,by decide⟩).lower)
        (by norm_num [cell12986]) (by norm_num [cell12986])
      exact ⟨E.1,E.2.trans (by norm_num [cell12986])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy26 (n := 12986) (by norm_num)
        (q := 1 - (cell12986 ⟨26,by decide⟩).lower)
        (by norm_num [cell12986]) (by norm_num [cell12986])
      exact ⟨E.1,E.2.trans (by norm_num [cell12986])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy27 (n := 12986) (by norm_num)
        (q := 1 - (cell12986 ⟨27,by decide⟩).lower)
        (by norm_num [cell12986]) (by norm_num [cell12986])
      exact ⟨E.1,E.2.trans (by norm_num [cell12986])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy28 (n := 12986) (by norm_num)
        (q := 1 - (cell12986 ⟨28,by decide⟩).lower)
        (by norm_num [cell12986]) (by norm_num [cell12986])
      exact ⟨E.1,E.2.trans (by norm_num [cell12986])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy29 (n := 12986) (by norm_num)
        (q := 1 - (cell12986 ⟨29,by decide⟩).lower)
        (by norm_num [cell12986]) (by norm_num [cell12986])
      exact ⟨E.1,E.2.trans (by norm_num [cell12986])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy30 (n := 12986) (by norm_num)
        (q := 1 - (cell12986 ⟨30,by decide⟩).lower)
        (by norm_num [cell12986]) (by norm_num [cell12986])
      exact ⟨E.1,E.2.trans (by norm_num [cell12986])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy31 (n := 12986) (by norm_num)
        (q := 1 - (cell12986 ⟨31,by decide⟩).lower)
        (by norm_num [cell12986]) (by norm_num [cell12986])
      exact ⟨E.1,E.2.trans (by norm_num [cell12986])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy32 (n := 12986) (by norm_num)
        (q := 1 - (cell12986 ⟨32,by decide⟩).lower)
        (by norm_num [cell12986]) (by norm_num [cell12986])
      exact ⟨E.1,E.2.trans (by norm_num [cell12986])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy33 (n := 12986) (by norm_num)
        (q := 1 - (cell12986 ⟨33,by decide⟩).lower)
        (by norm_num [cell12986]) (by norm_num [cell12986])
      exact ⟨E.1,E.2.trans (by norm_num [cell12986])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy34 (n := 12986) (by norm_num)
        (q := 1 - (cell12986 ⟨34,by decide⟩).lower)
        (by norm_num [cell12986]) (by norm_num [cell12986])
      exact ⟨E.1,E.2.trans (by norm_num [cell12986])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy35 (n := 12986) (by norm_num)
        (q := 1 - (cell12986 ⟨35,by decide⟩).lower)
        (by norm_num [cell12986]) (by norm_num [cell12986])
      exact ⟨E.1,E.2.trans (by norm_num [cell12986])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy36 (n := 12986) (by norm_num)
        (q := 1 - (cell12986 ⟨36,by decide⟩).lower)
        (by norm_num [cell12986]) (by norm_num [cell12986])
      exact ⟨E.1,E.2.trans (by norm_num [cell12986])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy37 (n := 12986) (by norm_num)
        (q := 1 - (cell12986 ⟨37,by decide⟩).lower)
        (by norm_num [cell12986]) (by norm_num [cell12986])
      exact ⟨E.1,E.2.trans (by norm_num [cell12986])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy38 (n := 12986) (by norm_num)
        (q := 1 - (cell12986 ⟨38,by decide⟩).lower)
        (by norm_num [cell12986]) (by norm_num [cell12986])
      exact ⟨E.1,E.2.trans (by norm_num [cell12986])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy39 (n := 12986) (by norm_num)
        (q := 1 - (cell12986 ⟨39,by decide⟩).lower)
        (by norm_num [cell12986]) (by norm_num [cell12986])
      exact ⟨E.1,E.2.trans (by norm_num [cell12986])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy40 (n := 12986) (by norm_num)
        (q := 1 - (cell12986 ⟨40,by decide⟩).lower)
        (by norm_num [cell12986]) (by norm_num [cell12986])
      exact ⟨E.1,E.2.trans (by norm_num [cell12986])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy41 (n := 12986) (by norm_num)
        (q := 1 - (cell12986 ⟨41,by decide⟩).lower)
        (by norm_num [cell12986]) (by norm_num [cell12986])
      exact ⟨E.1,E.2.trans (by norm_num [cell12986])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy42 (n := 12986) (by norm_num)
        (q := 1 - (cell12986 ⟨42,by decide⟩).lower)
        (by norm_num [cell12986]) (by norm_num [cell12986])
      exact ⟨E.1,E.2.trans (by norm_num [cell12986])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy43 (n := 12986) (by norm_num)
        (q := 1 - (cell12986 ⟨43,by decide⟩).lower)
        (by norm_num [cell12986]) (by norm_num [cell12986])
      exact ⟨E.1,E.2.trans (by norm_num [cell12986])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy44 (n := 12986) (by norm_num)
        (q := 1 - (cell12986 ⟨44,by decide⟩).lower)
        (by norm_num [cell12986]) (by norm_num [cell12986])
      exact ⟨E.1,E.2.trans (by norm_num [cell12986])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy45 (n := 12986) (by norm_num)
        (q := 1 - (cell12986 ⟨45,by decide⟩).lower)
        (by norm_num [cell12986]) (by norm_num [cell12986])
      exact ⟨E.1,E.2.trans (by norm_num [cell12986])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy46 (n := 12986) (by norm_num)
        (q := 1 - (cell12986 ⟨46,by decide⟩).lower)
        (by norm_num [cell12986]) (by norm_num [cell12986])
      exact ⟨E.1,E.2.trans (by norm_num [cell12986])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy47 (n := 12986) (by norm_num)
        (q := 1 - (cell12986 ⟨47,by decide⟩).lower)
        (by norm_num [cell12986]) (by norm_num [cell12986])
      exact ⟨E.1,E.2.trans (by norm_num [cell12986])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy48 (n := 12986) (by norm_num)
        (q := 1 - (cell12986 ⟨48,by decide⟩).lower)
        (by norm_num [cell12986]) (by norm_num [cell12986])
      exact ⟨E.1,E.2.trans (by norm_num [cell12986])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy49 (n := 12986) (by norm_num)
        (q := 1 - (cell12986 ⟨49,by decide⟩).lower)
        (by norm_num [cell12986]) (by norm_num [cell12986])
      exact ⟨E.1,E.2.trans (by norm_num [cell12986])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy50 (n := 12986) (by norm_num)
        (q := 1 - (cell12986 ⟨50,by decide⟩).lower)
        (by norm_num [cell12986]) (by norm_num [cell12986])
      exact ⟨E.1,E.2.trans (by norm_num [cell12986])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy51 (n := 12986) (by norm_num)
        (q := 1 - (cell12986 ⟨51,by decide⟩).lower)
        (by norm_num [cell12986]) (by norm_num [cell12986])
      exact ⟨E.1,E.2.trans (by norm_num [cell12986])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy52 (n := 12986) (by norm_num)
        (q := 1 - (cell12986 ⟨52,by decide⟩).lower)
        (by norm_num [cell12986]) (by norm_num [cell12986])
      exact ⟨E.1,E.2.trans (by norm_num [cell12986])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12986

/-! Source-cell containment and simple scalar guards at 12986. -/
namespace BstLean.Part269.N12986
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12986)
open BstLean.Part268 (cell12986)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12986 ⟨10,by decide⟩).lower ∧ (cell12986 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12986 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12986 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12986 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12986 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12986 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12986,cell12986,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12986 ⟨11,by decide⟩).lower ∧ (cell12986 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12986 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12986 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12986 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12986 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12986 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12986,cell12986,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12986 ⟨12,by decide⟩).lower ∧ (cell12986 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12986 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12986 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12986 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12986 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12986 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12986,cell12986,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12986 ⟨13,by decide⟩).lower ∧ (cell12986 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12986 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12986 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12986 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12986 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12986 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12986,cell12986,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12986 ⟨14,by decide⟩).lower ∧ (cell12986 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12986 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12986 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12986 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12986 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12986 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12986,cell12986,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12986 ⟨15,by decide⟩).lower ∧ (cell12986 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12986 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12986 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12986 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12986 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12986 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12986,cell12986,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12986 ⟨16,by decide⟩).lower ∧ (cell12986 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12986 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12986 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12986 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12986 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12986 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12986,cell12986,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12986 ⟨17,by decide⟩).lower ∧ (cell12986 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12986 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12986 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12986 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12986 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12986 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12986,cell12986,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12986 ⟨18,by decide⟩).lower ∧ (cell12986 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12986 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12986 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12986 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12986 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12986 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12986,cell12986,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12986 ⟨19,by decide⟩).lower ∧ (cell12986 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12986 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12986 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12986 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12986 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12986 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12986,cell12986,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12986 ⟨20,by decide⟩).lower ∧ (cell12986 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12986 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12986 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12986 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12986 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12986 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12986,cell12986,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12986 ⟨21,by decide⟩).lower ∧ (cell12986 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12986 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12986 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12986 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12986 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12986 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12986,cell12986,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12986 ⟨22,by decide⟩).lower ∧ (cell12986 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12986 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12986 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12986 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12986 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12986 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12986,cell12986,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12986 ⟨23,by decide⟩).lower ∧ (cell12986 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12986 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12986 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12986 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12986 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12986 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12986,cell12986,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12986 ⟨24,by decide⟩).lower ∧ (cell12986 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12986 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12986 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12986 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12986 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12986 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12986,cell12986,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12986 ⟨25,by decide⟩).lower ∧ (cell12986 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12986 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12986 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12986 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12986 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12986 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12986,cell12986,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12986 ⟨26,by decide⟩).lower ∧ (cell12986 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12986 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12986 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12986 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12986 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12986 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12986,cell12986,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12986 ⟨27,by decide⟩).lower ∧ (cell12986 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12986 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12986 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12986 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12986 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12986 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12986,cell12986,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12986 ⟨28,by decide⟩).lower ∧ (cell12986 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12986 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12986 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12986 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12986 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12986 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12986,cell12986,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12986 ⟨29,by decide⟩).lower ∧ (cell12986 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12986 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12986 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12986 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12986 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12986 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12986,cell12986,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12986 ⟨30,by decide⟩).lower ∧ (cell12986 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12986 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12986 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12986 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12986 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12986 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12986,cell12986,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12986 ⟨31,by decide⟩).lower ∧ (cell12986 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12986 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12986 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12986 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12986 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12986 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12986,cell12986,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12986 ⟨32,by decide⟩).lower ∧ (cell12986 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12986 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12986 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12986 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12986 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12986 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12986,cell12986,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12986 ⟨33,by decide⟩).lower ∧ (cell12986 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12986 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12986 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12986 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12986 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12986 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12986,cell12986,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12986 ⟨34,by decide⟩).lower ∧ (cell12986 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12986 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12986 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12986 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12986 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12986 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12986,cell12986,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12986 ⟨35,by decide⟩).lower ∧ (cell12986 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12986 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12986 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12986 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12986 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12986 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12986,cell12986,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12986 ⟨36,by decide⟩).lower ∧ (cell12986 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12986 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12986 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12986 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12986 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12986 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12986,cell12986,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12986 ⟨37,by decide⟩).lower ∧ (cell12986 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12986 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12986 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12986 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12986 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12986 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12986,cell12986,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12986 ⟨38,by decide⟩).lower ∧ (cell12986 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12986 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12986 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12986 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12986 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12986 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12986,cell12986,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12986 ⟨39,by decide⟩).lower ∧ (cell12986 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12986 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12986 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12986 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12986 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12986 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12986,cell12986,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12986 ⟨40,by decide⟩).lower ∧ (cell12986 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12986 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12986 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12986 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12986 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12986 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12986,cell12986,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12986 ⟨41,by decide⟩).lower ∧ (cell12986 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12986 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12986 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12986 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12986 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12986 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12986,cell12986,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12986 ⟨42,by decide⟩).lower ∧ (cell12986 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12986 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12986 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12986 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12986 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12986 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12986,cell12986,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12986 ⟨43,by decide⟩).lower ∧ (cell12986 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12986 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12986 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12986 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12986 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12986 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12986,cell12986,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12986 ⟨44,by decide⟩).lower ∧ (cell12986 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12986 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12986 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12986 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12986 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12986 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12986,cell12986,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12986 ⟨45,by decide⟩).lower ∧ (cell12986 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12986 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12986 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12986 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12986 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12986 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12986,cell12986,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12986 ⟨46,by decide⟩).lower ∧ (cell12986 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12986 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12986 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12986 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12986 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12986 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12986,cell12986,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12986 ⟨47,by decide⟩).lower ∧ (cell12986 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12986 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12986 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12986 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12986 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12986 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12986,cell12986,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12986 ⟨48,by decide⟩).lower ∧ (cell12986 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12986 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12986 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12986 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12986 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12986 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12986,cell12986,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12986 ⟨49,by decide⟩).lower ∧ (cell12986 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12986 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12986 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12986 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12986 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12986 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12986,cell12986,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12986 ⟨50,by decide⟩).lower ∧ (cell12986 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12986 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12986 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12986 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12986 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12986 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12986,cell12986,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12986 ⟨51,by decide⟩).lower ∧ (cell12986 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12986 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12986 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12986 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12986 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12986 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12986,cell12986,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12986 ⟨52,by decide⟩).lower ∧ (cell12986 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12986 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12986 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12986 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12986 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12986 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12986,cell12986,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12986 i).lower ∧
    (cell12986 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12986 i).upper ≤ (0.532 : ℝ) ∧
    (cell12986 i).centre ≤ (0.1 : ℝ) ∧ (cell12986 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12986 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12986 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12986

/-! The local source numeric instances at 12986 have no network premises. -/
namespace BstLean.Part269.N12986
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12986)
open BstLean.Part268 (cell12986)

noncomputable def sourceNumerics12986 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12986 (cell12986 i)
      scalarRow12986.M scalarRow12986.H scalarRow12986.xi := by
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
    energy_allowance := scalarRow12986.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12986]
    centre_nonneg := (scalarRow12986.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D25.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12986])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12986
/-! Actual 12987 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12987
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12987 ≤ (1.035407875408 : ℝ) := by
  have hr : (113.960519479335 : ℝ) ≤ √(12987 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.960519479335 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12987 12987 (11 / 1000) ≤
    (0.008387878120 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12987) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.960519479335 : ℝ) ≤ √(12987 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12987)
  have hdiv : K / √(12987 : ℝ) ≤ K / 113.960519479335 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.960519479335 ≤ (0.008387878120 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12987.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12987 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12987 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12987 := gPlus_lower 12987
end BstLean.Part269.N12987

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12987
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035407875407 : ℝ) ≤ wn 12987 := by
  have hn : √(12987 : ℝ) ≤ 113.960519479336 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12987 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.960519479336 ≤ 2 / √(12987 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000246219108 : ℝ) ≤ rhoBar 12987 BstLean.Part154.csC ∧
    rhoBar 12987 BstLean.Part154.csC ≤ 0.000246219490 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035407875407 : ℝ) / (1.295212 * 12987) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035407875408 : ℝ) / (1.29521 * 12987) := by gcongr
      _ ≤ (0.000246219490 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12987 BstLean.Part154.csC) ≤ 0.000984938585 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12987 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12987 BstLean.Part154.csC) (piBar (rhoBar 12987 BstLean.Part154.csC)) ≤ 0.000188063911 ∧
    cc1 (rhoBar 12987 BstLean.Part154.csC) (piBar (rhoBar 12987 BstLean.Part154.csC)) ≤ 0.000119666356 ∧
    cc2 (rhoBar 12987 BstLean.Part154.csC) ≤ 0.000069467285 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12987 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12987 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12987 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12987 BstLean.Part154.csC * nuR (rhoBar 12987 BstLean.Part154.csC)) ≤ 0.000492454137 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000246219490 : ℝ) * 0.000984938585 := by gcongr
      _ ≤ (0.000492454137 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12987 BstLean.Part154.csC) * nuR (rhoBar 12987 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000984938585 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12987 BstLean.Part154.csC) * rhoBar 12987 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000246219490 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000246219490 / 2 + 0.399 * 0.000984938585 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000188063911 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000492454137 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119666356 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000246219490 / 1.414213562 := by gcongr
      _ ≤ (0.000069467285 : ℝ) := by norm_num

end BstLean.Part269.N12987

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12987
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12987 BstLean.Part154.csC) (piBar (rhoBar 12987 BstLean.Part154.csC)) ≤ 1.52738E-7 := by
  have hr0 : 0 ≤ rhoBar 12987 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12987 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12987 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12987 BstLean.Part154.csC) (piBar (rhoBar 12987 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12987 BstLean.Part154.csC) (piBar (rhoBar 12987 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12987 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000188063911 : ℝ) ^ 2 + 0.000119666356 ^ 2 + 3 * 0.000069467285 ^ 2 +
        2 * 0.797885 * 0.000188063911 * 0.000119666356 + 2 * 0.000188063911 * 0.000069467285 +
        4 * 0.797885 * 0.000119666356 * 0.000069467285 := by gcongr
    _ ≤ (1.52738E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12987 BstLean.Part154.csC Θ ≤ 0.002569193421 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12987 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12987 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12987 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12987 BstLean.Part154.csC) (piBar (rhoBar 12987 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12987 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035407875408 * 1.52738E-7 / (0.000246219108 : ℝ) := by gcongr
    _ ≤ 0.002569193421 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12987 BstLean.Part154.csC Θ ≤ 0.002849548749 + 0.000649193401 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12987 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12987 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12987 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035407875408 : ℝ) * ((2 * Θ * 0.000246219490 +
        (6863 / 10000) * 0.000246219490 * 12987 * 0.000984938585) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002849548749 + 0.000649193401 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12987 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12987 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12987 0.011 Θ ∧ gammaRatio 12987 0.011 Θ ≤ 0.000084643894 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12987 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035407875408 : ℝ) * 0.525 / ((1 - 0.011) * 12987) := by gcongr
      _ ≤ (0.000084643894 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12987 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12987 0.011 Θ) :=
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
    badAllowance 12987 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000421835223 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12987 BstLean.Part154.csC) 1.22 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 2 (rhoBar 12987 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12987 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12987 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12987 0.011 Θ) 1.12 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 1 (gammaRatio 12987 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12987 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12987 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12987 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12987 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035407875408 : ℝ) * 12987 *
        (1.5230E-8 / 1.1045361 + 1.8602E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000421835223 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12987 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003271383972 + 0.003218386822 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12987

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12987
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12987 BstLean.Part154.csC) (piBar (rhoBar 12987 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12987 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12987 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12987 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12987 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12987 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12987 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12987 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12987 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12987 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12987 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12987 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12987 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12987 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12987 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051894893679 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12987) ≤ 0.010479397484 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12987 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035407875408)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010479397484 + 2 * 0.737676 / 12987) := by gcongr
    _ ≤ (0.051894893679 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12987 12 ≤ 0.0015 := by
  exact BstLean.Part269.S25.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12987

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12987
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560516260460 : ℝ) ≤ plow 12987 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12987) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052467637054)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001348826547) : eMP 12987 0.011 xi bn ≤ 0.001161596250 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12987 : ℝ) * (1 - 0.011))) ≤ 0.000574381505 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001348826547 / (12987 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000574381505 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000574381505 : ℝ) + 3.141593 * 0.052467637054 / (12987 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001161596250 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052467637054)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001348826547) : PiBarMP 12987 12 0.011 xi bn ≤ 0.159441648024 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12987 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036726373998 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.332003423569 : ℝ) ≤ √((12987 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.960519479335 : ℝ) ≤ √(12987 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12987) ≤ 0.122256447465 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036726373998 + 0.052467637054 * 1.772454 / (2 * (113.332003423569 : ℝ))) * (1 + 0.001161596250) +
        8 / (12987 * 113.960519479335) + 0.122256447465 := by gcongr
    _ ≤ (0.159441648024 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052467637054)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001348826547) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280953045802) :
    parallelOracle 12987 0.011 xi bn cd ≤ 0.160410155976 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12987 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12987 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560516260460 : ℝ) ≤ plow 12987 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.960519479335 : ℝ) ≤ √(12987 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280953045802 : ℝ) / (2 * 0.560516260460 * 113.960519479335)) * 0.159441648024 +
        0.280953045802 ^ 2 / (2 * 0.560516260460 * 113.960519479335) := by gcongr
    _ ≤ (0.160410155976 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052467637054) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001348826547)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280953045802) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12987 12987 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560516260460 : ℝ) ≤ plow 12987 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.960519479335 : ℝ) ≤ √(12987 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12987 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12987 Θ 1.22 ≤ 0.011636490480 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.960519479335 := by gcongr <;> linarith
      _ ≤ (0.011636490480 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12987 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12987 12987 0.011 ≤ 0.008387878120 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12987 12987 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12987 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12987 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12987 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12987 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160410155976 + 0.011636490480 + (0.008387878120 : ℝ) *
        (1 + 2 * (0.280953045802 + 0.011636490480) / (0.560516260460 * 113.960519479335))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12987]

end BstLean.Part269.N12987

/-! The original eight local profiles supply actual 12987 moment certificates. -/
namespace BstLean.Part269.N12987
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12987 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12987 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12987 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052467637054 ∧
    0 ≤ bN 12987 BstLean.Part154.csC (groupTheta g) ∧ bN 12987 BstLean.Part154.csC (groupTheta g) ≤ 0.001348826547 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12987 12987 0.011
      (momentAllowance 12987 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12987 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12987 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12987 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12987 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12987 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229058152123 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12987 0.011
      (momentAllowance 12987 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12987 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12987
/-! The actual computed-centre upper energy formula at 12987. -/
namespace BstLean.Part269.N12987
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12987

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12987
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12987)
open BstLean.Part268 (cell12987)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084694225349
  | 2 => 0.085623350401
  | 3 => 0.086548753443
  | 4 => 0.087471414949
  | 5 => 0.088392533755
  | 6 => 0.089313561097
  | 7 => 0.090236238158
  | 8 => 0.091162637217
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12987 12987 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12987 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003274156000 + 0.003221457154 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S25.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12987

/-! Actual upper energy certificates on all 43 source endpoints at 12987. -/
namespace BstLean.Part269.N12987
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12987)
open BstLean.Part268 (cell12987)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12987 (gMinus 12987) (1 - (cell12987 i).lower) ≤ 1 ∧
    energyUpper 12987 (gMinus 12987) (BstLean.Part211.gPlus 12987)
      (finiteEnergy 12987 12987 0.011) (1 - (cell12987 i).lower) ≤
      (cell12987 i).energy := by
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
      have E := BstLean.Part269.S25.uniformEnergy10 (n := 12987) (by norm_num)
        (q := 1 - (cell12987 ⟨10,by decide⟩).lower)
        (by norm_num [cell12987]) (by norm_num [cell12987])
      exact ⟨E.1,E.2.trans (by norm_num [cell12987])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy11 (n := 12987) (by norm_num)
        (q := 1 - (cell12987 ⟨11,by decide⟩).lower)
        (by norm_num [cell12987]) (by norm_num [cell12987])
      exact ⟨E.1,E.2.trans (by norm_num [cell12987])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy12 (n := 12987) (by norm_num)
        (q := 1 - (cell12987 ⟨12,by decide⟩).lower)
        (by norm_num [cell12987]) (by norm_num [cell12987])
      exact ⟨E.1,E.2.trans (by norm_num [cell12987])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy13 (n := 12987) (by norm_num)
        (q := 1 - (cell12987 ⟨13,by decide⟩).lower)
        (by norm_num [cell12987]) (by norm_num [cell12987])
      exact ⟨E.1,E.2.trans (by norm_num [cell12987])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy14 (n := 12987) (by norm_num)
        (q := 1 - (cell12987 ⟨14,by decide⟩).lower)
        (by norm_num [cell12987]) (by norm_num [cell12987])
      exact ⟨E.1,E.2.trans (by norm_num [cell12987])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy15 (n := 12987) (by norm_num)
        (q := 1 - (cell12987 ⟨15,by decide⟩).lower)
        (by norm_num [cell12987]) (by norm_num [cell12987])
      exact ⟨E.1,E.2.trans (by norm_num [cell12987])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy16 (n := 12987) (by norm_num)
        (q := 1 - (cell12987 ⟨16,by decide⟩).lower)
        (by norm_num [cell12987]) (by norm_num [cell12987])
      exact ⟨E.1,E.2.trans (by norm_num [cell12987])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy17 (n := 12987) (by norm_num)
        (q := 1 - (cell12987 ⟨17,by decide⟩).lower)
        (by norm_num [cell12987]) (by norm_num [cell12987])
      exact ⟨E.1,E.2.trans (by norm_num [cell12987])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy18 (n := 12987) (by norm_num)
        (q := 1 - (cell12987 ⟨18,by decide⟩).lower)
        (by norm_num [cell12987]) (by norm_num [cell12987])
      exact ⟨E.1,E.2.trans (by norm_num [cell12987])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy19 (n := 12987) (by norm_num)
        (q := 1 - (cell12987 ⟨19,by decide⟩).lower)
        (by norm_num [cell12987]) (by norm_num [cell12987])
      exact ⟨E.1,E.2.trans (by norm_num [cell12987])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy20 (n := 12987) (by norm_num)
        (q := 1 - (cell12987 ⟨20,by decide⟩).lower)
        (by norm_num [cell12987]) (by norm_num [cell12987])
      exact ⟨E.1,E.2.trans (by norm_num [cell12987])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy21 (n := 12987) (by norm_num)
        (q := 1 - (cell12987 ⟨21,by decide⟩).lower)
        (by norm_num [cell12987]) (by norm_num [cell12987])
      exact ⟨E.1,E.2.trans (by norm_num [cell12987])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy22 (n := 12987) (by norm_num)
        (q := 1 - (cell12987 ⟨22,by decide⟩).lower)
        (by norm_num [cell12987]) (by norm_num [cell12987])
      exact ⟨E.1,E.2.trans (by norm_num [cell12987])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy23 (n := 12987) (by norm_num)
        (q := 1 - (cell12987 ⟨23,by decide⟩).lower)
        (by norm_num [cell12987]) (by norm_num [cell12987])
      exact ⟨E.1,E.2.trans (by norm_num [cell12987])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy24 (n := 12987) (by norm_num)
        (q := 1 - (cell12987 ⟨24,by decide⟩).lower)
        (by norm_num [cell12987]) (by norm_num [cell12987])
      exact ⟨E.1,E.2.trans (by norm_num [cell12987])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy25 (n := 12987) (by norm_num)
        (q := 1 - (cell12987 ⟨25,by decide⟩).lower)
        (by norm_num [cell12987]) (by norm_num [cell12987])
      exact ⟨E.1,E.2.trans (by norm_num [cell12987])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy26 (n := 12987) (by norm_num)
        (q := 1 - (cell12987 ⟨26,by decide⟩).lower)
        (by norm_num [cell12987]) (by norm_num [cell12987])
      exact ⟨E.1,E.2.trans (by norm_num [cell12987])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy27 (n := 12987) (by norm_num)
        (q := 1 - (cell12987 ⟨27,by decide⟩).lower)
        (by norm_num [cell12987]) (by norm_num [cell12987])
      exact ⟨E.1,E.2.trans (by norm_num [cell12987])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy28 (n := 12987) (by norm_num)
        (q := 1 - (cell12987 ⟨28,by decide⟩).lower)
        (by norm_num [cell12987]) (by norm_num [cell12987])
      exact ⟨E.1,E.2.trans (by norm_num [cell12987])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy29 (n := 12987) (by norm_num)
        (q := 1 - (cell12987 ⟨29,by decide⟩).lower)
        (by norm_num [cell12987]) (by norm_num [cell12987])
      exact ⟨E.1,E.2.trans (by norm_num [cell12987])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy30 (n := 12987) (by norm_num)
        (q := 1 - (cell12987 ⟨30,by decide⟩).lower)
        (by norm_num [cell12987]) (by norm_num [cell12987])
      exact ⟨E.1,E.2.trans (by norm_num [cell12987])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy31 (n := 12987) (by norm_num)
        (q := 1 - (cell12987 ⟨31,by decide⟩).lower)
        (by norm_num [cell12987]) (by norm_num [cell12987])
      exact ⟨E.1,E.2.trans (by norm_num [cell12987])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy32 (n := 12987) (by norm_num)
        (q := 1 - (cell12987 ⟨32,by decide⟩).lower)
        (by norm_num [cell12987]) (by norm_num [cell12987])
      exact ⟨E.1,E.2.trans (by norm_num [cell12987])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy33 (n := 12987) (by norm_num)
        (q := 1 - (cell12987 ⟨33,by decide⟩).lower)
        (by norm_num [cell12987]) (by norm_num [cell12987])
      exact ⟨E.1,E.2.trans (by norm_num [cell12987])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy34 (n := 12987) (by norm_num)
        (q := 1 - (cell12987 ⟨34,by decide⟩).lower)
        (by norm_num [cell12987]) (by norm_num [cell12987])
      exact ⟨E.1,E.2.trans (by norm_num [cell12987])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy35 (n := 12987) (by norm_num)
        (q := 1 - (cell12987 ⟨35,by decide⟩).lower)
        (by norm_num [cell12987]) (by norm_num [cell12987])
      exact ⟨E.1,E.2.trans (by norm_num [cell12987])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy36 (n := 12987) (by norm_num)
        (q := 1 - (cell12987 ⟨36,by decide⟩).lower)
        (by norm_num [cell12987]) (by norm_num [cell12987])
      exact ⟨E.1,E.2.trans (by norm_num [cell12987])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy37 (n := 12987) (by norm_num)
        (q := 1 - (cell12987 ⟨37,by decide⟩).lower)
        (by norm_num [cell12987]) (by norm_num [cell12987])
      exact ⟨E.1,E.2.trans (by norm_num [cell12987])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy38 (n := 12987) (by norm_num)
        (q := 1 - (cell12987 ⟨38,by decide⟩).lower)
        (by norm_num [cell12987]) (by norm_num [cell12987])
      exact ⟨E.1,E.2.trans (by norm_num [cell12987])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy39 (n := 12987) (by norm_num)
        (q := 1 - (cell12987 ⟨39,by decide⟩).lower)
        (by norm_num [cell12987]) (by norm_num [cell12987])
      exact ⟨E.1,E.2.trans (by norm_num [cell12987])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy40 (n := 12987) (by norm_num)
        (q := 1 - (cell12987 ⟨40,by decide⟩).lower)
        (by norm_num [cell12987]) (by norm_num [cell12987])
      exact ⟨E.1,E.2.trans (by norm_num [cell12987])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy41 (n := 12987) (by norm_num)
        (q := 1 - (cell12987 ⟨41,by decide⟩).lower)
        (by norm_num [cell12987]) (by norm_num [cell12987])
      exact ⟨E.1,E.2.trans (by norm_num [cell12987])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy42 (n := 12987) (by norm_num)
        (q := 1 - (cell12987 ⟨42,by decide⟩).lower)
        (by norm_num [cell12987]) (by norm_num [cell12987])
      exact ⟨E.1,E.2.trans (by norm_num [cell12987])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy43 (n := 12987) (by norm_num)
        (q := 1 - (cell12987 ⟨43,by decide⟩).lower)
        (by norm_num [cell12987]) (by norm_num [cell12987])
      exact ⟨E.1,E.2.trans (by norm_num [cell12987])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy44 (n := 12987) (by norm_num)
        (q := 1 - (cell12987 ⟨44,by decide⟩).lower)
        (by norm_num [cell12987]) (by norm_num [cell12987])
      exact ⟨E.1,E.2.trans (by norm_num [cell12987])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy45 (n := 12987) (by norm_num)
        (q := 1 - (cell12987 ⟨45,by decide⟩).lower)
        (by norm_num [cell12987]) (by norm_num [cell12987])
      exact ⟨E.1,E.2.trans (by norm_num [cell12987])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy46 (n := 12987) (by norm_num)
        (q := 1 - (cell12987 ⟨46,by decide⟩).lower)
        (by norm_num [cell12987]) (by norm_num [cell12987])
      exact ⟨E.1,E.2.trans (by norm_num [cell12987])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy47 (n := 12987) (by norm_num)
        (q := 1 - (cell12987 ⟨47,by decide⟩).lower)
        (by norm_num [cell12987]) (by norm_num [cell12987])
      exact ⟨E.1,E.2.trans (by norm_num [cell12987])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy48 (n := 12987) (by norm_num)
        (q := 1 - (cell12987 ⟨48,by decide⟩).lower)
        (by norm_num [cell12987]) (by norm_num [cell12987])
      exact ⟨E.1,E.2.trans (by norm_num [cell12987])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy49 (n := 12987) (by norm_num)
        (q := 1 - (cell12987 ⟨49,by decide⟩).lower)
        (by norm_num [cell12987]) (by norm_num [cell12987])
      exact ⟨E.1,E.2.trans (by norm_num [cell12987])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy50 (n := 12987) (by norm_num)
        (q := 1 - (cell12987 ⟨50,by decide⟩).lower)
        (by norm_num [cell12987]) (by norm_num [cell12987])
      exact ⟨E.1,E.2.trans (by norm_num [cell12987])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy51 (n := 12987) (by norm_num)
        (q := 1 - (cell12987 ⟨51,by decide⟩).lower)
        (by norm_num [cell12987]) (by norm_num [cell12987])
      exact ⟨E.1,E.2.trans (by norm_num [cell12987])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy52 (n := 12987) (by norm_num)
        (q := 1 - (cell12987 ⟨52,by decide⟩).lower)
        (by norm_num [cell12987]) (by norm_num [cell12987])
      exact ⟨E.1,E.2.trans (by norm_num [cell12987])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12987

/-! Source-cell containment and simple scalar guards at 12987. -/
namespace BstLean.Part269.N12987
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12987)
open BstLean.Part268 (cell12987)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12987 ⟨10,by decide⟩).lower ∧ (cell12987 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12987 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12987 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12987 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12987 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12987 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12987,cell12987,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12987 ⟨11,by decide⟩).lower ∧ (cell12987 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12987 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12987 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12987 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12987 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12987 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12987,cell12987,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12987 ⟨12,by decide⟩).lower ∧ (cell12987 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12987 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12987 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12987 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12987 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12987 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12987,cell12987,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12987 ⟨13,by decide⟩).lower ∧ (cell12987 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12987 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12987 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12987 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12987 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12987 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12987,cell12987,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12987 ⟨14,by decide⟩).lower ∧ (cell12987 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12987 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12987 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12987 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12987 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12987 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12987,cell12987,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12987 ⟨15,by decide⟩).lower ∧ (cell12987 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12987 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12987 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12987 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12987 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12987 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12987,cell12987,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12987 ⟨16,by decide⟩).lower ∧ (cell12987 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12987 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12987 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12987 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12987 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12987 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12987,cell12987,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12987 ⟨17,by decide⟩).lower ∧ (cell12987 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12987 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12987 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12987 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12987 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12987 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12987,cell12987,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12987 ⟨18,by decide⟩).lower ∧ (cell12987 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12987 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12987 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12987 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12987 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12987 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12987,cell12987,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12987 ⟨19,by decide⟩).lower ∧ (cell12987 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12987 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12987 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12987 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12987 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12987 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12987,cell12987,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12987 ⟨20,by decide⟩).lower ∧ (cell12987 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12987 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12987 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12987 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12987 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12987 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12987,cell12987,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12987 ⟨21,by decide⟩).lower ∧ (cell12987 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12987 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12987 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12987 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12987 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12987 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12987,cell12987,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12987 ⟨22,by decide⟩).lower ∧ (cell12987 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12987 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12987 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12987 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12987 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12987 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12987,cell12987,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12987 ⟨23,by decide⟩).lower ∧ (cell12987 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12987 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12987 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12987 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12987 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12987 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12987,cell12987,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12987 ⟨24,by decide⟩).lower ∧ (cell12987 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12987 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12987 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12987 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12987 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12987 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12987,cell12987,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12987 ⟨25,by decide⟩).lower ∧ (cell12987 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12987 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12987 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12987 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12987 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12987 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12987,cell12987,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12987 ⟨26,by decide⟩).lower ∧ (cell12987 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12987 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12987 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12987 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12987 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12987 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12987,cell12987,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12987 ⟨27,by decide⟩).lower ∧ (cell12987 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12987 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12987 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12987 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12987 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12987 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12987,cell12987,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12987 ⟨28,by decide⟩).lower ∧ (cell12987 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12987 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12987 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12987 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12987 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12987 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12987,cell12987,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12987 ⟨29,by decide⟩).lower ∧ (cell12987 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12987 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12987 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12987 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12987 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12987 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12987,cell12987,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12987 ⟨30,by decide⟩).lower ∧ (cell12987 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12987 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12987 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12987 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12987 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12987 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12987,cell12987,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12987 ⟨31,by decide⟩).lower ∧ (cell12987 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12987 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12987 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12987 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12987 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12987 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12987,cell12987,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12987 ⟨32,by decide⟩).lower ∧ (cell12987 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12987 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12987 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12987 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12987 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12987 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12987,cell12987,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12987 ⟨33,by decide⟩).lower ∧ (cell12987 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12987 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12987 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12987 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12987 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12987 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12987,cell12987,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12987 ⟨34,by decide⟩).lower ∧ (cell12987 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12987 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12987 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12987 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12987 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12987 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12987,cell12987,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12987 ⟨35,by decide⟩).lower ∧ (cell12987 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12987 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12987 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12987 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12987 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12987 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12987,cell12987,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12987 ⟨36,by decide⟩).lower ∧ (cell12987 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12987 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12987 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12987 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12987 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12987 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12987,cell12987,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12987 ⟨37,by decide⟩).lower ∧ (cell12987 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12987 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12987 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12987 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12987 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12987 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12987,cell12987,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12987 ⟨38,by decide⟩).lower ∧ (cell12987 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12987 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12987 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12987 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12987 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12987 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12987,cell12987,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12987 ⟨39,by decide⟩).lower ∧ (cell12987 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12987 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12987 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12987 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12987 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12987 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12987,cell12987,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12987 ⟨40,by decide⟩).lower ∧ (cell12987 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12987 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12987 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12987 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12987 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12987 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12987,cell12987,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12987 ⟨41,by decide⟩).lower ∧ (cell12987 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12987 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12987 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12987 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12987 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12987 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12987,cell12987,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12987 ⟨42,by decide⟩).lower ∧ (cell12987 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12987 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12987 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12987 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12987 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12987 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12987,cell12987,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12987 ⟨43,by decide⟩).lower ∧ (cell12987 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12987 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12987 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12987 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12987 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12987 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12987,cell12987,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12987 ⟨44,by decide⟩).lower ∧ (cell12987 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12987 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12987 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12987 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12987 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12987 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12987,cell12987,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12987 ⟨45,by decide⟩).lower ∧ (cell12987 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12987 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12987 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12987 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12987 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12987 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12987,cell12987,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12987 ⟨46,by decide⟩).lower ∧ (cell12987 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12987 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12987 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12987 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12987 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12987 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12987,cell12987,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12987 ⟨47,by decide⟩).lower ∧ (cell12987 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12987 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12987 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12987 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12987 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12987 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12987,cell12987,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12987 ⟨48,by decide⟩).lower ∧ (cell12987 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12987 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12987 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12987 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12987 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12987 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12987,cell12987,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12987 ⟨49,by decide⟩).lower ∧ (cell12987 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12987 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12987 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12987 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12987 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12987 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12987,cell12987,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12987 ⟨50,by decide⟩).lower ∧ (cell12987 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12987 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12987 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12987 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12987 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12987 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12987,cell12987,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12987 ⟨51,by decide⟩).lower ∧ (cell12987 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12987 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12987 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12987 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12987 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12987 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12987,cell12987,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12987 ⟨52,by decide⟩).lower ∧ (cell12987 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12987 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12987 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12987 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12987 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12987 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12987,cell12987,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12987 i).lower ∧
    (cell12987 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12987 i).upper ≤ (0.532 : ℝ) ∧
    (cell12987 i).centre ≤ (0.1 : ℝ) ∧ (cell12987 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12987 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12987 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12987

/-! The local source numeric instances at 12987 have no network premises. -/
namespace BstLean.Part269.N12987
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12987)
open BstLean.Part268 (cell12987)

noncomputable def sourceNumerics12987 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12987 (cell12987 i)
      scalarRow12987.M scalarRow12987.H scalarRow12987.xi := by
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
    energy_allowance := scalarRow12987.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12987]
    centre_nonneg := (scalarRow12987.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D25.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12987])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12987