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
/-! Actual 13038 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13038
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13038 ≤ (1.035337954268 : ℝ) := by
  have hr : (114.184061935105 : ℝ) ≤ √(13038 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.184061935105 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13038 13038 (11 / 1000) ≤
    (0.008371456731 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13038) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.184061935105 : ℝ) ≤ √(13038 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13038)
  have hdiv : K / √(13038 : ℝ) ≤ K / 114.184061935105 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.184061935105 ≤ (0.008371456731 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13038.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13038 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13038 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13038 := gPlus_lower 13038
end BstLean.Part269.N13038

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13038
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035337954267 : ℝ) ≤ wn 13038 := by
  have hn : √(13038 : ℝ) ≤ 114.184061935106 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13038 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.184061935106 ≤ 2 / √(13038 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000245239425 : ℝ) ≤ rhoBar 13038 BstLean.Part154.csC ∧
    rhoBar 13038 BstLean.Part154.csC ≤ 0.000245239805 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035337954267 : ℝ) / (1.295212 * 13038) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035337954268 : ℝ) / (1.29521 * 13038) := by gcongr
      _ ≤ (0.000245239805 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13038 BstLean.Part154.csC) ≤ 0.000981019363 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13038 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13038 BstLean.Part154.csC) (piBar (rhoBar 13038 BstLean.Part154.csC)) ≤ 0.000187315588 ∧
    cc1 (rhoBar 13038 BstLean.Part154.csC) (piBar (rhoBar 13038 BstLean.Part154.csC)) ≤ 0.000119190199 ∧
    cc2 (rhoBar 13038 BstLean.Part154.csC) ≤ 0.000069190881 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13038 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13038 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13038 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13038 BstLean.Part154.csC * nuR (rhoBar 13038 BstLean.Part154.csC)) ≤ 0.000490494646 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000245239805 : ℝ) * 0.000981019363 := by gcongr
      _ ≤ (0.000490494646 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13038 BstLean.Part154.csC) * nuR (rhoBar 13038 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000981019363 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13038 BstLean.Part154.csC) * rhoBar 13038 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000245239805 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000245239805 / 2 + 0.399 * 0.000981019363 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000187315588 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000490494646 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119190199 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000245239805 / 1.414213562 := by gcongr
      _ ≤ (0.000069190881 : ℝ) := by norm_num

end BstLean.Part269.N13038

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13038
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13038 BstLean.Part154.csC) (piBar (rhoBar 13038 BstLean.Part154.csC)) ≤ 1.51525E-7 := by
  have hr0 : 0 ≤ rhoBar 13038 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13038 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13038 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13038 BstLean.Part154.csC) (piBar (rhoBar 13038 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13038 BstLean.Part154.csC) (piBar (rhoBar 13038 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13038 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000187315588 : ℝ) ^ 2 + 0.000119190199 ^ 2 + 3 * 0.000069190881 ^ 2 +
        2 * 0.797885 * 0.000187315588 * 0.000119190199 + 2 * 0.000187315588 * 0.000069190881 +
        4 * 0.797885 * 0.000119190199 * 0.000069190881 := by gcongr
    _ ≤ (1.51525E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13038 BstLean.Part154.csC Θ ≤ 0.002558798750 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13038 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13038 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13038 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13038 BstLean.Part154.csC) (piBar (rhoBar 13038 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13038 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035337954268 * 1.51525E-7 / (0.000245239425 : ℝ) := by gcongr
    _ ≤ 0.002558798750 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13038 BstLean.Part154.csC Θ ≤ 0.002837826639 + 0.000646566653 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13038 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13038 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13038 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035337954268 : ℝ) * ((2 * Θ * 0.000245239805 +
        (6863 / 10000) * 0.000245239805 * 13038 * 0.000981019363) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002837826639 + 0.000646566653 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13038 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13038 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13038 0.011 Θ ∧ gammaRatio 13038 0.011 Θ ≤ 0.000084307103 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13038 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035337954268 : ℝ) * 0.525 / ((1 - 0.011) * 13038) := by gcongr
      _ ≤ (0.000084307103 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13038 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13038 0.011 Θ) :=
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
    badAllowance 13038 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000383431726 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13038 BstLean.Part154.csC) 1.22 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 2 (rhoBar 13038 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13038 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13038 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13038 0.011 Θ) 1.12 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 1 (gammaRatio 13038 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13038 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13038 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13038 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13038 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035337954268 : ℝ) * 13038 *
        (1.3781E-8 / 1.1045361 + 1.6832E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000383431726 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13038 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003221258365 + 0.003205365403 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13038

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13038
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13038 BstLean.Part154.csC) (piBar (rhoBar 13038 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13038 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13038 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13038 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13038 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13038 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13038 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13038 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13038 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13038 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13038 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13038 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13038 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13038 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13038 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051792209665 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13038) ≤ 0.010458881571 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13038 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035337954268)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010458881571 + 2 * 0.737676 / 13038) := by gcongr
    _ ≤ (0.051792209665 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13038 12 ≤ 0.0015 := by
  exact BstLean.Part269.S27.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13038

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13038
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560518457393 : ℝ) ≤ plow 13038 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13038) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052410675202)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001343369344) : eMP 13038 0.011 xi bn ≤ 0.001156961511 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13038 : ℝ) * (1 - 0.011))) ≤ 0.000572096174 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001343369344 / (13038 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000572096174 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000572096174 : ℝ) + 3.141593 * 0.052410675202 / (13038 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001156961511 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052410675202)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001343369344) : PiBarMP 13038 12 0.011 xi bn ≤ 0.159126392158 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13038 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036652003275 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.554312996028 : ℝ) ≤ √((13038 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.184061935105 : ℝ) ≤ √(13038 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13038) ≤ 0.122017101395 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036652003275 + 0.052410675202 * 1.772454 / (2 * (113.554312996028 : ℝ))) * (1 + 0.001156961511) +
        8 / (13038 * 114.184061935105) + 0.122017101395 := by gcongr
    _ ≤ (0.159126392158 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052410675202)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001343369344) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280725988741) :
    parallelOracle 13038 0.011 xi bn cd ≤ 0.160091029712 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13038 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13038 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560518457393 : ℝ) ≤ plow 13038 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.184061935105 : ℝ) ≤ √(13038 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280725988741 : ℝ) / (2 * 0.560518457393 * 114.184061935105)) * 0.159126392158 +
        0.280725988741 ^ 2 / (2 * 0.560518457393 * 114.184061935105) := by gcongr
    _ ≤ (0.160091029712 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052410675202) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001343369344)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280725988741) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13038 13038 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560518457393 : ℝ) ≤ plow 13038 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.184061935105 : ℝ) ≤ √(13038 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13038 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13038 Θ 1.22 ≤ 0.011613709283 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.184061935105 := by gcongr <;> linarith
      _ ≤ (0.011613709283 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13038 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13038 13038 0.011 ≤ 0.008371456731 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13038 13038 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13038 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13038 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13038 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13038 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160091029712 + 0.011613709283 + (0.008371456731 : ℝ) *
        (1 + 2 * (0.280725988741 + 0.011613709283) / (0.560518457393 * 114.184061935105))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13038]

end BstLean.Part269.N13038

/-! The original eight local profiles supply actual 13038 moment certificates. -/
namespace BstLean.Part269.N13038
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13038 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13038 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13038 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052410675202 ∧
    0 ≤ bN 13038 BstLean.Part154.csC (groupTheta g) ∧ bN 13038 BstLean.Part154.csC (groupTheta g) ≤ 0.001343369344 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13038 13038 0.011
      (momentAllowance 13038 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13038 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13038 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13038 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13038 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13038 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228933779076 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13038 0.011
      (momentAllowance 13038 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13038 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13038
/-! The actual computed-centre upper energy formula at 13038. -/
namespace BstLean.Part269.N13038
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13038

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13038
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13038)
open BstLean.Part268 (cell13038)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084561183802
  | 2 => 0.085488564048
  | 3 => 0.086411958342
  | 4 => 0.087332285259
  | 5 => 0.088250670432
  | 6 => 0.089168479095
  | 7 => 0.090087352047
  | 8 => 0.091009245118
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13038 13038 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13038 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N13038

/-! Actual upper energy certificates on all 43 source endpoints at 13038. -/
namespace BstLean.Part269.N13038
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13038)
open BstLean.Part268 (cell13038)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13038 (gMinus 13038) (1 - (cell13038 i).lower) ≤ 1 ∧
    energyUpper 13038 (gMinus 13038) (BstLean.Part211.gPlus 13038)
      (finiteEnergy 13038 13038 0.011) (1 - (cell13038 i).lower) ≤
      (cell13038 i).energy := by
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
      have E := BstLean.Part269.S27.uniformEnergy10 (n := 13038) (by norm_num)
        (q := 1 - (cell13038 ⟨10,by decide⟩).lower)
        (by norm_num [cell13038]) (by norm_num [cell13038])
      exact ⟨E.1,E.2.trans (by norm_num [cell13038])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy11 (n := 13038) (by norm_num)
        (q := 1 - (cell13038 ⟨11,by decide⟩).lower)
        (by norm_num [cell13038]) (by norm_num [cell13038])
      exact ⟨E.1,E.2.trans (by norm_num [cell13038])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy12 (n := 13038) (by norm_num)
        (q := 1 - (cell13038 ⟨12,by decide⟩).lower)
        (by norm_num [cell13038]) (by norm_num [cell13038])
      exact ⟨E.1,E.2.trans (by norm_num [cell13038])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy13 (n := 13038) (by norm_num)
        (q := 1 - (cell13038 ⟨13,by decide⟩).lower)
        (by norm_num [cell13038]) (by norm_num [cell13038])
      exact ⟨E.1,E.2.trans (by norm_num [cell13038])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy14 (n := 13038) (by norm_num)
        (q := 1 - (cell13038 ⟨14,by decide⟩).lower)
        (by norm_num [cell13038]) (by norm_num [cell13038])
      exact ⟨E.1,E.2.trans (by norm_num [cell13038])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy15 (n := 13038) (by norm_num)
        (q := 1 - (cell13038 ⟨15,by decide⟩).lower)
        (by norm_num [cell13038]) (by norm_num [cell13038])
      exact ⟨E.1,E.2.trans (by norm_num [cell13038])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy16 (n := 13038) (by norm_num)
        (q := 1 - (cell13038 ⟨16,by decide⟩).lower)
        (by norm_num [cell13038]) (by norm_num [cell13038])
      exact ⟨E.1,E.2.trans (by norm_num [cell13038])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy17 (n := 13038) (by norm_num)
        (q := 1 - (cell13038 ⟨17,by decide⟩).lower)
        (by norm_num [cell13038]) (by norm_num [cell13038])
      exact ⟨E.1,E.2.trans (by norm_num [cell13038])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy18 (n := 13038) (by norm_num)
        (q := 1 - (cell13038 ⟨18,by decide⟩).lower)
        (by norm_num [cell13038]) (by norm_num [cell13038])
      exact ⟨E.1,E.2.trans (by norm_num [cell13038])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy19 (n := 13038) (by norm_num)
        (q := 1 - (cell13038 ⟨19,by decide⟩).lower)
        (by norm_num [cell13038]) (by norm_num [cell13038])
      exact ⟨E.1,E.2.trans (by norm_num [cell13038])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy20 (n := 13038) (by norm_num)
        (q := 1 - (cell13038 ⟨20,by decide⟩).lower)
        (by norm_num [cell13038]) (by norm_num [cell13038])
      exact ⟨E.1,E.2.trans (by norm_num [cell13038])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy21 (n := 13038) (by norm_num)
        (q := 1 - (cell13038 ⟨21,by decide⟩).lower)
        (by norm_num [cell13038]) (by norm_num [cell13038])
      exact ⟨E.1,E.2.trans (by norm_num [cell13038])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy22 (n := 13038) (by norm_num)
        (q := 1 - (cell13038 ⟨22,by decide⟩).lower)
        (by norm_num [cell13038]) (by norm_num [cell13038])
      exact ⟨E.1,E.2.trans (by norm_num [cell13038])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy23 (n := 13038) (by norm_num)
        (q := 1 - (cell13038 ⟨23,by decide⟩).lower)
        (by norm_num [cell13038]) (by norm_num [cell13038])
      exact ⟨E.1,E.2.trans (by norm_num [cell13038])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy24 (n := 13038) (by norm_num)
        (q := 1 - (cell13038 ⟨24,by decide⟩).lower)
        (by norm_num [cell13038]) (by norm_num [cell13038])
      exact ⟨E.1,E.2.trans (by norm_num [cell13038])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy25 (n := 13038) (by norm_num)
        (q := 1 - (cell13038 ⟨25,by decide⟩).lower)
        (by norm_num [cell13038]) (by norm_num [cell13038])
      exact ⟨E.1,E.2.trans (by norm_num [cell13038])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy26 (n := 13038) (by norm_num)
        (q := 1 - (cell13038 ⟨26,by decide⟩).lower)
        (by norm_num [cell13038]) (by norm_num [cell13038])
      exact ⟨E.1,E.2.trans (by norm_num [cell13038])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy27 (n := 13038) (by norm_num)
        (q := 1 - (cell13038 ⟨27,by decide⟩).lower)
        (by norm_num [cell13038]) (by norm_num [cell13038])
      exact ⟨E.1,E.2.trans (by norm_num [cell13038])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy28 (n := 13038) (by norm_num)
        (q := 1 - (cell13038 ⟨28,by decide⟩).lower)
        (by norm_num [cell13038]) (by norm_num [cell13038])
      exact ⟨E.1,E.2.trans (by norm_num [cell13038])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy29 (n := 13038) (by norm_num)
        (q := 1 - (cell13038 ⟨29,by decide⟩).lower)
        (by norm_num [cell13038]) (by norm_num [cell13038])
      exact ⟨E.1,E.2.trans (by norm_num [cell13038])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy30 (n := 13038) (by norm_num)
        (q := 1 - (cell13038 ⟨30,by decide⟩).lower)
        (by norm_num [cell13038]) (by norm_num [cell13038])
      exact ⟨E.1,E.2.trans (by norm_num [cell13038])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy31 (n := 13038) (by norm_num)
        (q := 1 - (cell13038 ⟨31,by decide⟩).lower)
        (by norm_num [cell13038]) (by norm_num [cell13038])
      exact ⟨E.1,E.2.trans (by norm_num [cell13038])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy32 (n := 13038) (by norm_num)
        (q := 1 - (cell13038 ⟨32,by decide⟩).lower)
        (by norm_num [cell13038]) (by norm_num [cell13038])
      exact ⟨E.1,E.2.trans (by norm_num [cell13038])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy33 (n := 13038) (by norm_num)
        (q := 1 - (cell13038 ⟨33,by decide⟩).lower)
        (by norm_num [cell13038]) (by norm_num [cell13038])
      exact ⟨E.1,E.2.trans (by norm_num [cell13038])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy34 (n := 13038) (by norm_num)
        (q := 1 - (cell13038 ⟨34,by decide⟩).lower)
        (by norm_num [cell13038]) (by norm_num [cell13038])
      exact ⟨E.1,E.2.trans (by norm_num [cell13038])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy35 (n := 13038) (by norm_num)
        (q := 1 - (cell13038 ⟨35,by decide⟩).lower)
        (by norm_num [cell13038]) (by norm_num [cell13038])
      exact ⟨E.1,E.2.trans (by norm_num [cell13038])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy36 (n := 13038) (by norm_num)
        (q := 1 - (cell13038 ⟨36,by decide⟩).lower)
        (by norm_num [cell13038]) (by norm_num [cell13038])
      exact ⟨E.1,E.2.trans (by norm_num [cell13038])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy37 (n := 13038) (by norm_num)
        (q := 1 - (cell13038 ⟨37,by decide⟩).lower)
        (by norm_num [cell13038]) (by norm_num [cell13038])
      exact ⟨E.1,E.2.trans (by norm_num [cell13038])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy38 (n := 13038) (by norm_num)
        (q := 1 - (cell13038 ⟨38,by decide⟩).lower)
        (by norm_num [cell13038]) (by norm_num [cell13038])
      exact ⟨E.1,E.2.trans (by norm_num [cell13038])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy39 (n := 13038) (by norm_num)
        (q := 1 - (cell13038 ⟨39,by decide⟩).lower)
        (by norm_num [cell13038]) (by norm_num [cell13038])
      exact ⟨E.1,E.2.trans (by norm_num [cell13038])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy40 (n := 13038) (by norm_num)
        (q := 1 - (cell13038 ⟨40,by decide⟩).lower)
        (by norm_num [cell13038]) (by norm_num [cell13038])
      exact ⟨E.1,E.2.trans (by norm_num [cell13038])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy41 (n := 13038) (by norm_num)
        (q := 1 - (cell13038 ⟨41,by decide⟩).lower)
        (by norm_num [cell13038]) (by norm_num [cell13038])
      exact ⟨E.1,E.2.trans (by norm_num [cell13038])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy42 (n := 13038) (by norm_num)
        (q := 1 - (cell13038 ⟨42,by decide⟩).lower)
        (by norm_num [cell13038]) (by norm_num [cell13038])
      exact ⟨E.1,E.2.trans (by norm_num [cell13038])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy43 (n := 13038) (by norm_num)
        (q := 1 - (cell13038 ⟨43,by decide⟩).lower)
        (by norm_num [cell13038]) (by norm_num [cell13038])
      exact ⟨E.1,E.2.trans (by norm_num [cell13038])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy44 (n := 13038) (by norm_num)
        (q := 1 - (cell13038 ⟨44,by decide⟩).lower)
        (by norm_num [cell13038]) (by norm_num [cell13038])
      exact ⟨E.1,E.2.trans (by norm_num [cell13038])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy45 (n := 13038) (by norm_num)
        (q := 1 - (cell13038 ⟨45,by decide⟩).lower)
        (by norm_num [cell13038]) (by norm_num [cell13038])
      exact ⟨E.1,E.2.trans (by norm_num [cell13038])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy46 (n := 13038) (by norm_num)
        (q := 1 - (cell13038 ⟨46,by decide⟩).lower)
        (by norm_num [cell13038]) (by norm_num [cell13038])
      exact ⟨E.1,E.2.trans (by norm_num [cell13038])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy47 (n := 13038) (by norm_num)
        (q := 1 - (cell13038 ⟨47,by decide⟩).lower)
        (by norm_num [cell13038]) (by norm_num [cell13038])
      exact ⟨E.1,E.2.trans (by norm_num [cell13038])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy48 (n := 13038) (by norm_num)
        (q := 1 - (cell13038 ⟨48,by decide⟩).lower)
        (by norm_num [cell13038]) (by norm_num [cell13038])
      exact ⟨E.1,E.2.trans (by norm_num [cell13038])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy49 (n := 13038) (by norm_num)
        (q := 1 - (cell13038 ⟨49,by decide⟩).lower)
        (by norm_num [cell13038]) (by norm_num [cell13038])
      exact ⟨E.1,E.2.trans (by norm_num [cell13038])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy50 (n := 13038) (by norm_num)
        (q := 1 - (cell13038 ⟨50,by decide⟩).lower)
        (by norm_num [cell13038]) (by norm_num [cell13038])
      exact ⟨E.1,E.2.trans (by norm_num [cell13038])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy51 (n := 13038) (by norm_num)
        (q := 1 - (cell13038 ⟨51,by decide⟩).lower)
        (by norm_num [cell13038]) (by norm_num [cell13038])
      exact ⟨E.1,E.2.trans (by norm_num [cell13038])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy52 (n := 13038) (by norm_num)
        (q := 1 - (cell13038 ⟨52,by decide⟩).lower)
        (by norm_num [cell13038]) (by norm_num [cell13038])
      exact ⟨E.1,E.2.trans (by norm_num [cell13038])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13038

/-! Source-cell containment and simple scalar guards at 13038. -/
namespace BstLean.Part269.N13038
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13038)
open BstLean.Part268 (cell13038)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13038 ⟨10,by decide⟩).lower ∧ (cell13038 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13038 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13038 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13038 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13038 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13038 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13038,cell13038,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13038 ⟨11,by decide⟩).lower ∧ (cell13038 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13038 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13038 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13038 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13038 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13038 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13038,cell13038,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13038 ⟨12,by decide⟩).lower ∧ (cell13038 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13038 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13038 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13038 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13038 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13038 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13038,cell13038,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13038 ⟨13,by decide⟩).lower ∧ (cell13038 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13038 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13038 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13038 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13038 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13038 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13038,cell13038,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13038 ⟨14,by decide⟩).lower ∧ (cell13038 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13038 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13038 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13038 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13038 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13038 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13038,cell13038,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13038 ⟨15,by decide⟩).lower ∧ (cell13038 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13038 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13038 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13038 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13038 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13038 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13038,cell13038,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13038 ⟨16,by decide⟩).lower ∧ (cell13038 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13038 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13038 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13038 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13038 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13038 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13038,cell13038,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13038 ⟨17,by decide⟩).lower ∧ (cell13038 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13038 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13038 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13038 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13038 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13038 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13038,cell13038,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13038 ⟨18,by decide⟩).lower ∧ (cell13038 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13038 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13038 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13038 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13038 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13038 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13038,cell13038,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13038 ⟨19,by decide⟩).lower ∧ (cell13038 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13038 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13038 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13038 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13038 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13038 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13038,cell13038,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13038 ⟨20,by decide⟩).lower ∧ (cell13038 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13038 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13038 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13038 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13038 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13038 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13038,cell13038,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13038 ⟨21,by decide⟩).lower ∧ (cell13038 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13038 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13038 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13038 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13038 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13038 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13038,cell13038,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13038 ⟨22,by decide⟩).lower ∧ (cell13038 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13038 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13038 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13038 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13038 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13038 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13038,cell13038,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13038 ⟨23,by decide⟩).lower ∧ (cell13038 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13038 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13038 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13038 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13038 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13038 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13038,cell13038,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13038 ⟨24,by decide⟩).lower ∧ (cell13038 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13038 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13038 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13038 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13038 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13038 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13038,cell13038,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13038 ⟨25,by decide⟩).lower ∧ (cell13038 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13038 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13038 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13038 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13038 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13038 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13038,cell13038,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13038 ⟨26,by decide⟩).lower ∧ (cell13038 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13038 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13038 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13038 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13038 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13038 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13038,cell13038,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13038 ⟨27,by decide⟩).lower ∧ (cell13038 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13038 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13038 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13038 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13038 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13038 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13038,cell13038,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13038 ⟨28,by decide⟩).lower ∧ (cell13038 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13038 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13038 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13038 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13038 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13038 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13038,cell13038,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13038 ⟨29,by decide⟩).lower ∧ (cell13038 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13038 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13038 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13038 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13038 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13038 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13038,cell13038,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13038 ⟨30,by decide⟩).lower ∧ (cell13038 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13038 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13038 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13038 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13038 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13038 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13038,cell13038,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13038 ⟨31,by decide⟩).lower ∧ (cell13038 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13038 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13038 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13038 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13038 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13038 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13038,cell13038,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13038 ⟨32,by decide⟩).lower ∧ (cell13038 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13038 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13038 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13038 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13038 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13038 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13038,cell13038,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13038 ⟨33,by decide⟩).lower ∧ (cell13038 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13038 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13038 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13038 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13038 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13038 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13038,cell13038,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13038 ⟨34,by decide⟩).lower ∧ (cell13038 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13038 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13038 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13038 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13038 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13038 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13038,cell13038,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13038 ⟨35,by decide⟩).lower ∧ (cell13038 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13038 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13038 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13038 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13038 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13038 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13038,cell13038,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13038 ⟨36,by decide⟩).lower ∧ (cell13038 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13038 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13038 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13038 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13038 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13038 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13038,cell13038,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13038 ⟨37,by decide⟩).lower ∧ (cell13038 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13038 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13038 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13038 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13038 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13038 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13038,cell13038,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13038 ⟨38,by decide⟩).lower ∧ (cell13038 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13038 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13038 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13038 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13038 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13038 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13038,cell13038,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13038 ⟨39,by decide⟩).lower ∧ (cell13038 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13038 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13038 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13038 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13038 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13038 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13038,cell13038,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13038 ⟨40,by decide⟩).lower ∧ (cell13038 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13038 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13038 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13038 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13038 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13038 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13038,cell13038,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13038 ⟨41,by decide⟩).lower ∧ (cell13038 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13038 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13038 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13038 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13038 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13038 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13038,cell13038,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13038 ⟨42,by decide⟩).lower ∧ (cell13038 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13038 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13038 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13038 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13038 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13038 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13038,cell13038,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13038 ⟨43,by decide⟩).lower ∧ (cell13038 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13038 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13038 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13038 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13038 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13038 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13038,cell13038,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13038 ⟨44,by decide⟩).lower ∧ (cell13038 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13038 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13038 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13038 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13038 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13038 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13038,cell13038,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13038 ⟨45,by decide⟩).lower ∧ (cell13038 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13038 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13038 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13038 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13038 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13038 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13038,cell13038,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13038 ⟨46,by decide⟩).lower ∧ (cell13038 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13038 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13038 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13038 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13038 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13038 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13038,cell13038,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13038 ⟨47,by decide⟩).lower ∧ (cell13038 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13038 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13038 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13038 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13038 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13038 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13038,cell13038,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13038 ⟨48,by decide⟩).lower ∧ (cell13038 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13038 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13038 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13038 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13038 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13038 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13038,cell13038,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13038 ⟨49,by decide⟩).lower ∧ (cell13038 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13038 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13038 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13038 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13038 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13038 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13038,cell13038,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13038 ⟨50,by decide⟩).lower ∧ (cell13038 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13038 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13038 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13038 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13038 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13038 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13038,cell13038,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13038 ⟨51,by decide⟩).lower ∧ (cell13038 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13038 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13038 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13038 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13038 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13038 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13038,cell13038,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13038 ⟨52,by decide⟩).lower ∧ (cell13038 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13038 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13038 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13038 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13038 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13038 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13038,cell13038,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13038 i).lower ∧
    (cell13038 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13038 i).upper ≤ (0.532 : ℝ) ∧
    (cell13038 i).centre ≤ (0.1 : ℝ) ∧ (cell13038 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13038 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13038 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13038

/-! The local source numeric instances at 13038 have no network premises. -/
namespace BstLean.Part269.N13038
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13038)
open BstLean.Part268 (cell13038)

noncomputable def sourceNumerics13038 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13038 (cell13038 i)
      scalarRow13038.M scalarRow13038.H scalarRow13038.xi := by
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
    energy_allowance := scalarRow13038.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13038]
    centre_nonneg := (scalarRow13038.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D27.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13038])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13038
/-! Actual 13039 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13039
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13039 ≤ (1.035336587391 : ℝ) := by
  have hr : (114.188440745987 : ℝ) ≤ √(13039 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.188440745987 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13039 13039 (11 / 1000) ≤
    (0.008371135706 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13039) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.188440745987 : ℝ) ≤ √(13039 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13039)
  have hdiv : K / √(13039 : ℝ) ≤ K / 114.188440745987 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.188440745987 ≤ (0.008371135706 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13039.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13039 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13039 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13039 := gPlus_lower 13039
end BstLean.Part269.N13039

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13039
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035336587390 : ℝ) ≤ wn 13039 := by
  have hn : √(13039 : ℝ) ≤ 114.188440745988 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13039 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.188440745988 ≤ 2 / √(13039 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000245220293 : ℝ) ≤ rhoBar 13039 BstLean.Part154.csC ∧
    rhoBar 13039 BstLean.Part154.csC ≤ 0.000245220673 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035336587390 : ℝ) / (1.295212 * 13039) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035336587391 : ℝ) / (1.29521 * 13039) := by gcongr
      _ ≤ (0.000245220673 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13039 BstLean.Part154.csC) ≤ 0.000980942826 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13039 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13039 BstLean.Part154.csC) (piBar (rhoBar 13039 BstLean.Part154.csC)) ≤ 0.000187300974 ∧
    cc1 (rhoBar 13039 BstLean.Part154.csC) (piBar (rhoBar 13039 BstLean.Part154.csC)) ≤ 0.000119180901 ∧
    cc2 (rhoBar 13039 BstLean.Part154.csC) ≤ 0.000069185484 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13039 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13039 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13039 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13039 BstLean.Part154.csC * nuR (rhoBar 13039 BstLean.Part154.csC)) ≤ 0.000490456380 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000245220673 : ℝ) * 0.000980942826 := by gcongr
      _ ≤ (0.000490456380 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13039 BstLean.Part154.csC) * nuR (rhoBar 13039 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000980942826 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13039 BstLean.Part154.csC) * rhoBar 13039 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000245220673 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000245220673 / 2 + 0.399 * 0.000980942826 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000187300974 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000490456380 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119180901 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000245220673 / 1.414213562 := by gcongr
      _ ≤ (0.000069185484 : ℝ) := by norm_num

end BstLean.Part269.N13039

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13039
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13039 BstLean.Part154.csC) (piBar (rhoBar 13039 BstLean.Part154.csC)) ≤ 1.51501E-7 := by
  have hr0 : 0 ≤ rhoBar 13039 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13039 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13039 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13039 BstLean.Part154.csC) (piBar (rhoBar 13039 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13039 BstLean.Part154.csC) (piBar (rhoBar 13039 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13039 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000187300974 : ℝ) ^ 2 + 0.000119180901 ^ 2 + 3 * 0.000069185484 ^ 2 +
        2 * 0.797885 * 0.000187300974 * 0.000119180901 + 2 * 0.000187300974 * 0.000069185484 +
        4 * 0.797885 * 0.000119180901 * 0.000069185484 := by gcongr
    _ ≤ (1.51501E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13039 BstLean.Part154.csC Θ ≤ 0.002558589690 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13039 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13039 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13039 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13039 BstLean.Part154.csC) (piBar (rhoBar 13039 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13039 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035336587391 * 1.51501E-7 / (0.000245220293 : ℝ) := by gcongr
    _ ≤ 0.002558589690 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13039 BstLean.Part154.csC Θ ≤ 0.002837597745 + 0.000646515359 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13039 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13039 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13039 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035336587391 : ℝ) * ((2 * Θ * 0.000245220673 +
        (6863 / 10000) * 0.000245220673 * 13039 * 0.000980942826) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002837597745 + 0.000646515359 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13039 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13039 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13039 0.011 Θ ∧ gammaRatio 13039 0.011 Θ ≤ 0.000084300526 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13039 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035336587391 : ℝ) * 0.525 / ((1 - 0.011) * 13039) := by gcongr
      _ ≤ (0.000084300526 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13039 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13039 0.011 Θ) :=
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
    badAllowance 13039 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000383431726 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13039 BstLean.Part154.csC) 1.22 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 2 (rhoBar 13039 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13039 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13039 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13039 0.011 Θ) 1.12 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 1 (gammaRatio 13039 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13039 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13039 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13039 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13039 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035336587391 : ℝ) * 13039 *
        (1.3781E-8 / 1.1045361 + 1.6832E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000383431726 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13039 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003221029471 + 0.003205105049 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13039

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13039
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13039 BstLean.Part154.csC) (piBar (rhoBar 13039 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13039 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13039 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13039 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13039 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13039 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13039 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13039 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13039 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13039 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13039 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13039 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13039 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13039 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13039 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051790202321 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13039) ≤ 0.010458480502 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13039 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035336587391)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010458480502 + 2 * 0.737676 / 13039) := by gcongr
    _ ≤ (0.051790202321 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13039 12 ≤ 0.0015 := by
  exact BstLean.Part269.S27.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13039

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13039
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560518500299 : ℝ) ≤ plow 13039 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13039) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052410309622)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001343259588) : eMP 13039 0.011 xi bn ≤ 0.001156869824 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13039 : ℝ) * (1 - 0.011))) ≤ 0.000572050865 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001343259588 / (13039 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000572050865 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000572050865 : ℝ) + 3.141593 * 0.052410309622 / (13039 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001156869824 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052410309622)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001343259588) : PiBarMP 13039 12 0.011 xi bn ≤ 0.159120191527 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13039 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036650505972 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.558667656854 : ℝ) ≤ √((13039 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.188440745987 : ℝ) ≤ √(13039 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13039) ≤ 0.122012422376 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036650505972 + 0.052410309622 * 1.772454 / (2 * (113.558667656854 : ℝ))) * (1 + 0.001156869824) +
        8 / (13039 * 114.188440745987) + 0.122012422376 := by gcongr
    _ ≤ (0.159120191527 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052410309622)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001343259588) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280723182956) :
    parallelOracle 13039 0.011 xi bn cd ≤ 0.160084762624 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13039 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13039 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560518500299 : ℝ) ≤ plow 13039 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.188440745987 : ℝ) ≤ √(13039 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280723182956 : ℝ) / (2 * 0.560518500299 * 114.188440745987)) * 0.159120191527 +
        0.280723182956 ^ 2 / (2 * 0.560518500299 * 114.188440745987) := by gcongr
    _ ≤ (0.160084762624 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052410309622) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001343259588)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280723182956) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13039 13039 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560518500299 : ℝ) ≤ plow 13039 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.188440745987 : ℝ) ≤ √(13039 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13039 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13039 Θ 1.22 ≤ 0.011613263929 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.188440745987 := by gcongr <;> linarith
      _ ≤ (0.011613263929 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13039 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13039 13039 0.011 ≤ 0.008371135706 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13039 13039 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13039 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13039 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13039 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13039 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160084762624 + 0.011613263929 + (0.008371135706 : ℝ) *
        (1 + 2 * (0.280723182956 + 0.011613263929) / (0.560518500299 * 114.188440745987))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13039]

end BstLean.Part269.N13039

/-! The original eight local profiles supply actual 13039 moment certificates. -/
namespace BstLean.Part269.N13039
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13039 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13039 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13039 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052410309622 ∧
    0 ≤ bN 13039 BstLean.Part154.csC (groupTheta g) ∧ bN 13039 BstLean.Part154.csC (groupTheta g) ≤ 0.001343259588 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13039 13039 0.011
      (momentAllowance 13039 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13039 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13039 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13039 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13039 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13039 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228932980635 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13039 0.011
      (momentAllowance 13039 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13039 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13039
/-! The actual computed-centre upper energy formula at 13039. -/
namespace BstLean.Part269.N13039
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13039

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13039
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13039)
open BstLean.Part268 (cell13039)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084558595735
  | 2 => 0.085485942491
  | 3 => 0.086409298293
  | 4 => 0.087329580540
  | 5 => 0.088247913470
  | 6 => 0.089165660680
  | 7 => 0.090084461056
  | 8 => 0.091006268206
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13039 13039 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13039 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N13039

/-! Actual upper energy certificates on all 43 source endpoints at 13039. -/
namespace BstLean.Part269.N13039
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13039)
open BstLean.Part268 (cell13039)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13039 (gMinus 13039) (1 - (cell13039 i).lower) ≤ 1 ∧
    energyUpper 13039 (gMinus 13039) (BstLean.Part211.gPlus 13039)
      (finiteEnergy 13039 13039 0.011) (1 - (cell13039 i).lower) ≤
      (cell13039 i).energy := by
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
      have E := BstLean.Part269.S27.uniformEnergy10 (n := 13039) (by norm_num)
        (q := 1 - (cell13039 ⟨10,by decide⟩).lower)
        (by norm_num [cell13039]) (by norm_num [cell13039])
      exact ⟨E.1,E.2.trans (by norm_num [cell13039])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy11 (n := 13039) (by norm_num)
        (q := 1 - (cell13039 ⟨11,by decide⟩).lower)
        (by norm_num [cell13039]) (by norm_num [cell13039])
      exact ⟨E.1,E.2.trans (by norm_num [cell13039])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy12 (n := 13039) (by norm_num)
        (q := 1 - (cell13039 ⟨12,by decide⟩).lower)
        (by norm_num [cell13039]) (by norm_num [cell13039])
      exact ⟨E.1,E.2.trans (by norm_num [cell13039])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy13 (n := 13039) (by norm_num)
        (q := 1 - (cell13039 ⟨13,by decide⟩).lower)
        (by norm_num [cell13039]) (by norm_num [cell13039])
      exact ⟨E.1,E.2.trans (by norm_num [cell13039])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy14 (n := 13039) (by norm_num)
        (q := 1 - (cell13039 ⟨14,by decide⟩).lower)
        (by norm_num [cell13039]) (by norm_num [cell13039])
      exact ⟨E.1,E.2.trans (by norm_num [cell13039])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy15 (n := 13039) (by norm_num)
        (q := 1 - (cell13039 ⟨15,by decide⟩).lower)
        (by norm_num [cell13039]) (by norm_num [cell13039])
      exact ⟨E.1,E.2.trans (by norm_num [cell13039])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy16 (n := 13039) (by norm_num)
        (q := 1 - (cell13039 ⟨16,by decide⟩).lower)
        (by norm_num [cell13039]) (by norm_num [cell13039])
      exact ⟨E.1,E.2.trans (by norm_num [cell13039])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy17 (n := 13039) (by norm_num)
        (q := 1 - (cell13039 ⟨17,by decide⟩).lower)
        (by norm_num [cell13039]) (by norm_num [cell13039])
      exact ⟨E.1,E.2.trans (by norm_num [cell13039])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy18 (n := 13039) (by norm_num)
        (q := 1 - (cell13039 ⟨18,by decide⟩).lower)
        (by norm_num [cell13039]) (by norm_num [cell13039])
      exact ⟨E.1,E.2.trans (by norm_num [cell13039])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy19 (n := 13039) (by norm_num)
        (q := 1 - (cell13039 ⟨19,by decide⟩).lower)
        (by norm_num [cell13039]) (by norm_num [cell13039])
      exact ⟨E.1,E.2.trans (by norm_num [cell13039])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy20 (n := 13039) (by norm_num)
        (q := 1 - (cell13039 ⟨20,by decide⟩).lower)
        (by norm_num [cell13039]) (by norm_num [cell13039])
      exact ⟨E.1,E.2.trans (by norm_num [cell13039])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy21 (n := 13039) (by norm_num)
        (q := 1 - (cell13039 ⟨21,by decide⟩).lower)
        (by norm_num [cell13039]) (by norm_num [cell13039])
      exact ⟨E.1,E.2.trans (by norm_num [cell13039])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy22 (n := 13039) (by norm_num)
        (q := 1 - (cell13039 ⟨22,by decide⟩).lower)
        (by norm_num [cell13039]) (by norm_num [cell13039])
      exact ⟨E.1,E.2.trans (by norm_num [cell13039])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy23 (n := 13039) (by norm_num)
        (q := 1 - (cell13039 ⟨23,by decide⟩).lower)
        (by norm_num [cell13039]) (by norm_num [cell13039])
      exact ⟨E.1,E.2.trans (by norm_num [cell13039])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy24 (n := 13039) (by norm_num)
        (q := 1 - (cell13039 ⟨24,by decide⟩).lower)
        (by norm_num [cell13039]) (by norm_num [cell13039])
      exact ⟨E.1,E.2.trans (by norm_num [cell13039])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy25 (n := 13039) (by norm_num)
        (q := 1 - (cell13039 ⟨25,by decide⟩).lower)
        (by norm_num [cell13039]) (by norm_num [cell13039])
      exact ⟨E.1,E.2.trans (by norm_num [cell13039])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy26 (n := 13039) (by norm_num)
        (q := 1 - (cell13039 ⟨26,by decide⟩).lower)
        (by norm_num [cell13039]) (by norm_num [cell13039])
      exact ⟨E.1,E.2.trans (by norm_num [cell13039])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy27 (n := 13039) (by norm_num)
        (q := 1 - (cell13039 ⟨27,by decide⟩).lower)
        (by norm_num [cell13039]) (by norm_num [cell13039])
      exact ⟨E.1,E.2.trans (by norm_num [cell13039])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy28 (n := 13039) (by norm_num)
        (q := 1 - (cell13039 ⟨28,by decide⟩).lower)
        (by norm_num [cell13039]) (by norm_num [cell13039])
      exact ⟨E.1,E.2.trans (by norm_num [cell13039])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy29 (n := 13039) (by norm_num)
        (q := 1 - (cell13039 ⟨29,by decide⟩).lower)
        (by norm_num [cell13039]) (by norm_num [cell13039])
      exact ⟨E.1,E.2.trans (by norm_num [cell13039])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy30 (n := 13039) (by norm_num)
        (q := 1 - (cell13039 ⟨30,by decide⟩).lower)
        (by norm_num [cell13039]) (by norm_num [cell13039])
      exact ⟨E.1,E.2.trans (by norm_num [cell13039])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy31 (n := 13039) (by norm_num)
        (q := 1 - (cell13039 ⟨31,by decide⟩).lower)
        (by norm_num [cell13039]) (by norm_num [cell13039])
      exact ⟨E.1,E.2.trans (by norm_num [cell13039])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy32 (n := 13039) (by norm_num)
        (q := 1 - (cell13039 ⟨32,by decide⟩).lower)
        (by norm_num [cell13039]) (by norm_num [cell13039])
      exact ⟨E.1,E.2.trans (by norm_num [cell13039])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy33 (n := 13039) (by norm_num)
        (q := 1 - (cell13039 ⟨33,by decide⟩).lower)
        (by norm_num [cell13039]) (by norm_num [cell13039])
      exact ⟨E.1,E.2.trans (by norm_num [cell13039])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy34 (n := 13039) (by norm_num)
        (q := 1 - (cell13039 ⟨34,by decide⟩).lower)
        (by norm_num [cell13039]) (by norm_num [cell13039])
      exact ⟨E.1,E.2.trans (by norm_num [cell13039])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy35 (n := 13039) (by norm_num)
        (q := 1 - (cell13039 ⟨35,by decide⟩).lower)
        (by norm_num [cell13039]) (by norm_num [cell13039])
      exact ⟨E.1,E.2.trans (by norm_num [cell13039])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy36 (n := 13039) (by norm_num)
        (q := 1 - (cell13039 ⟨36,by decide⟩).lower)
        (by norm_num [cell13039]) (by norm_num [cell13039])
      exact ⟨E.1,E.2.trans (by norm_num [cell13039])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy37 (n := 13039) (by norm_num)
        (q := 1 - (cell13039 ⟨37,by decide⟩).lower)
        (by norm_num [cell13039]) (by norm_num [cell13039])
      exact ⟨E.1,E.2.trans (by norm_num [cell13039])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy38 (n := 13039) (by norm_num)
        (q := 1 - (cell13039 ⟨38,by decide⟩).lower)
        (by norm_num [cell13039]) (by norm_num [cell13039])
      exact ⟨E.1,E.2.trans (by norm_num [cell13039])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy39 (n := 13039) (by norm_num)
        (q := 1 - (cell13039 ⟨39,by decide⟩).lower)
        (by norm_num [cell13039]) (by norm_num [cell13039])
      exact ⟨E.1,E.2.trans (by norm_num [cell13039])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy40 (n := 13039) (by norm_num)
        (q := 1 - (cell13039 ⟨40,by decide⟩).lower)
        (by norm_num [cell13039]) (by norm_num [cell13039])
      exact ⟨E.1,E.2.trans (by norm_num [cell13039])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy41 (n := 13039) (by norm_num)
        (q := 1 - (cell13039 ⟨41,by decide⟩).lower)
        (by norm_num [cell13039]) (by norm_num [cell13039])
      exact ⟨E.1,E.2.trans (by norm_num [cell13039])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy42 (n := 13039) (by norm_num)
        (q := 1 - (cell13039 ⟨42,by decide⟩).lower)
        (by norm_num [cell13039]) (by norm_num [cell13039])
      exact ⟨E.1,E.2.trans (by norm_num [cell13039])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy43 (n := 13039) (by norm_num)
        (q := 1 - (cell13039 ⟨43,by decide⟩).lower)
        (by norm_num [cell13039]) (by norm_num [cell13039])
      exact ⟨E.1,E.2.trans (by norm_num [cell13039])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy44 (n := 13039) (by norm_num)
        (q := 1 - (cell13039 ⟨44,by decide⟩).lower)
        (by norm_num [cell13039]) (by norm_num [cell13039])
      exact ⟨E.1,E.2.trans (by norm_num [cell13039])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy45 (n := 13039) (by norm_num)
        (q := 1 - (cell13039 ⟨45,by decide⟩).lower)
        (by norm_num [cell13039]) (by norm_num [cell13039])
      exact ⟨E.1,E.2.trans (by norm_num [cell13039])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy46 (n := 13039) (by norm_num)
        (q := 1 - (cell13039 ⟨46,by decide⟩).lower)
        (by norm_num [cell13039]) (by norm_num [cell13039])
      exact ⟨E.1,E.2.trans (by norm_num [cell13039])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy47 (n := 13039) (by norm_num)
        (q := 1 - (cell13039 ⟨47,by decide⟩).lower)
        (by norm_num [cell13039]) (by norm_num [cell13039])
      exact ⟨E.1,E.2.trans (by norm_num [cell13039])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy48 (n := 13039) (by norm_num)
        (q := 1 - (cell13039 ⟨48,by decide⟩).lower)
        (by norm_num [cell13039]) (by norm_num [cell13039])
      exact ⟨E.1,E.2.trans (by norm_num [cell13039])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy49 (n := 13039) (by norm_num)
        (q := 1 - (cell13039 ⟨49,by decide⟩).lower)
        (by norm_num [cell13039]) (by norm_num [cell13039])
      exact ⟨E.1,E.2.trans (by norm_num [cell13039])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy50 (n := 13039) (by norm_num)
        (q := 1 - (cell13039 ⟨50,by decide⟩).lower)
        (by norm_num [cell13039]) (by norm_num [cell13039])
      exact ⟨E.1,E.2.trans (by norm_num [cell13039])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy51 (n := 13039) (by norm_num)
        (q := 1 - (cell13039 ⟨51,by decide⟩).lower)
        (by norm_num [cell13039]) (by norm_num [cell13039])
      exact ⟨E.1,E.2.trans (by norm_num [cell13039])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy52 (n := 13039) (by norm_num)
        (q := 1 - (cell13039 ⟨52,by decide⟩).lower)
        (by norm_num [cell13039]) (by norm_num [cell13039])
      exact ⟨E.1,E.2.trans (by norm_num [cell13039])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13039

/-! Source-cell containment and simple scalar guards at 13039. -/
namespace BstLean.Part269.N13039
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13039)
open BstLean.Part268 (cell13039)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13039 ⟨10,by decide⟩).lower ∧ (cell13039 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13039 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13039 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13039 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13039 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13039 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13039,cell13039,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13039 ⟨11,by decide⟩).lower ∧ (cell13039 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13039 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13039 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13039 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13039 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13039 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13039,cell13039,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13039 ⟨12,by decide⟩).lower ∧ (cell13039 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13039 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13039 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13039 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13039 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13039 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13039,cell13039,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13039 ⟨13,by decide⟩).lower ∧ (cell13039 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13039 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13039 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13039 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13039 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13039 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13039,cell13039,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13039 ⟨14,by decide⟩).lower ∧ (cell13039 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13039 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13039 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13039 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13039 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13039 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13039,cell13039,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13039 ⟨15,by decide⟩).lower ∧ (cell13039 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13039 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13039 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13039 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13039 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13039 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13039,cell13039,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13039 ⟨16,by decide⟩).lower ∧ (cell13039 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13039 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13039 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13039 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13039 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13039 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13039,cell13039,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13039 ⟨17,by decide⟩).lower ∧ (cell13039 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13039 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13039 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13039 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13039 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13039 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13039,cell13039,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13039 ⟨18,by decide⟩).lower ∧ (cell13039 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13039 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13039 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13039 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13039 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13039 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13039,cell13039,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13039 ⟨19,by decide⟩).lower ∧ (cell13039 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13039 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13039 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13039 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13039 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13039 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13039,cell13039,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13039 ⟨20,by decide⟩).lower ∧ (cell13039 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13039 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13039 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13039 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13039 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13039 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13039,cell13039,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13039 ⟨21,by decide⟩).lower ∧ (cell13039 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13039 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13039 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13039 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13039 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13039 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13039,cell13039,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13039 ⟨22,by decide⟩).lower ∧ (cell13039 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13039 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13039 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13039 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13039 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13039 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13039,cell13039,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13039 ⟨23,by decide⟩).lower ∧ (cell13039 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13039 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13039 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13039 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13039 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13039 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13039,cell13039,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13039 ⟨24,by decide⟩).lower ∧ (cell13039 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13039 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13039 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13039 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13039 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13039 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13039,cell13039,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13039 ⟨25,by decide⟩).lower ∧ (cell13039 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13039 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13039 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13039 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13039 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13039 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13039,cell13039,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13039 ⟨26,by decide⟩).lower ∧ (cell13039 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13039 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13039 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13039 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13039 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13039 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13039,cell13039,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13039 ⟨27,by decide⟩).lower ∧ (cell13039 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13039 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13039 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13039 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13039 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13039 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13039,cell13039,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13039 ⟨28,by decide⟩).lower ∧ (cell13039 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13039 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13039 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13039 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13039 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13039 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13039,cell13039,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13039 ⟨29,by decide⟩).lower ∧ (cell13039 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13039 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13039 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13039 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13039 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13039 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13039,cell13039,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13039 ⟨30,by decide⟩).lower ∧ (cell13039 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13039 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13039 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13039 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13039 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13039 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13039,cell13039,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13039 ⟨31,by decide⟩).lower ∧ (cell13039 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13039 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13039 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13039 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13039 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13039 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13039,cell13039,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13039 ⟨32,by decide⟩).lower ∧ (cell13039 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13039 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13039 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13039 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13039 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13039 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13039,cell13039,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13039 ⟨33,by decide⟩).lower ∧ (cell13039 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13039 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13039 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13039 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13039 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13039 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13039,cell13039,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13039 ⟨34,by decide⟩).lower ∧ (cell13039 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13039 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13039 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13039 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13039 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13039 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13039,cell13039,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13039 ⟨35,by decide⟩).lower ∧ (cell13039 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13039 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13039 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13039 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13039 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13039 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13039,cell13039,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13039 ⟨36,by decide⟩).lower ∧ (cell13039 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13039 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13039 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13039 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13039 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13039 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13039,cell13039,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13039 ⟨37,by decide⟩).lower ∧ (cell13039 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13039 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13039 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13039 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13039 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13039 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13039,cell13039,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13039 ⟨38,by decide⟩).lower ∧ (cell13039 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13039 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13039 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13039 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13039 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13039 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13039,cell13039,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13039 ⟨39,by decide⟩).lower ∧ (cell13039 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13039 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13039 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13039 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13039 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13039 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13039,cell13039,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13039 ⟨40,by decide⟩).lower ∧ (cell13039 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13039 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13039 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13039 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13039 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13039 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13039,cell13039,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13039 ⟨41,by decide⟩).lower ∧ (cell13039 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13039 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13039 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13039 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13039 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13039 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13039,cell13039,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13039 ⟨42,by decide⟩).lower ∧ (cell13039 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13039 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13039 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13039 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13039 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13039 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13039,cell13039,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13039 ⟨43,by decide⟩).lower ∧ (cell13039 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13039 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13039 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13039 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13039 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13039 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13039,cell13039,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13039 ⟨44,by decide⟩).lower ∧ (cell13039 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13039 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13039 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13039 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13039 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13039 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13039,cell13039,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13039 ⟨45,by decide⟩).lower ∧ (cell13039 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13039 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13039 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13039 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13039 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13039 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13039,cell13039,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13039 ⟨46,by decide⟩).lower ∧ (cell13039 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13039 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13039 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13039 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13039 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13039 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13039,cell13039,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13039 ⟨47,by decide⟩).lower ∧ (cell13039 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13039 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13039 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13039 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13039 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13039 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13039,cell13039,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13039 ⟨48,by decide⟩).lower ∧ (cell13039 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13039 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13039 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13039 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13039 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13039 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13039,cell13039,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13039 ⟨49,by decide⟩).lower ∧ (cell13039 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13039 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13039 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13039 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13039 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13039 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13039,cell13039,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13039 ⟨50,by decide⟩).lower ∧ (cell13039 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13039 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13039 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13039 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13039 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13039 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13039,cell13039,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13039 ⟨51,by decide⟩).lower ∧ (cell13039 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13039 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13039 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13039 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13039 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13039 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13039,cell13039,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13039 ⟨52,by decide⟩).lower ∧ (cell13039 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13039 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13039 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13039 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13039 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13039 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13039,cell13039,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13039 i).lower ∧
    (cell13039 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13039 i).upper ≤ (0.532 : ℝ) ∧
    (cell13039 i).centre ≤ (0.1 : ℝ) ∧ (cell13039 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13039 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13039 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13039

/-! The local source numeric instances at 13039 have no network premises. -/
namespace BstLean.Part269.N13039
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13039)
open BstLean.Part268 (cell13039)

noncomputable def sourceNumerics13039 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13039 (cell13039 i)
      scalarRow13039.M scalarRow13039.H scalarRow13039.xi := by
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
    energy_allowance := scalarRow13039.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13039]
    centre_nonneg := (scalarRow13039.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D27.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13039])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13039
/-! Actual 13040 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13040
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13040 ≤ (1.035335220672 : ℝ) := by
  have hr : (114.192819388961 : ℝ) ≤ √(13040 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.192819388961 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13040 13040 (11 / 1000) ≤
    (0.008370814719 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13040) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.192819388961 : ℝ) ≤ √(13040 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13040)
  have hdiv : K / √(13040 : ℝ) ≤ K / 114.192819388961 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.192819388961 ≤ (0.008370814719 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13040.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13040 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13040 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13040 := gPlus_lower 13040
end BstLean.Part269.N13040

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13040
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035335220671 : ℝ) ≤ wn 13040 := by
  have hn : √(13040 : ℝ) ≤ 114.192819388962 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13040 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.192819388962 ≤ 2 / √(13040 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000245201164 : ℝ) ≤ rhoBar 13040 BstLean.Part154.csC ∧
    rhoBar 13040 BstLean.Part154.csC ≤ 0.000245201544 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035335220671 : ℝ) / (1.295212 * 13040) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035335220672 : ℝ) / (1.29521 * 13040) := by gcongr
      _ ≤ (0.000245201544 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13040 BstLean.Part154.csC) ≤ 0.000980866300 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13040 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13040 BstLean.Part154.csC) (piBar (rhoBar 13040 BstLean.Part154.csC)) ≤ 0.000187286362 ∧
    cc1 (rhoBar 13040 BstLean.Part154.csC) (piBar (rhoBar 13040 BstLean.Part154.csC)) ≤ 0.000119171603 ∧
    cc2 (rhoBar 13040 BstLean.Part154.csC) ≤ 0.000069180087 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13040 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13040 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13040 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13040 BstLean.Part154.csC * nuR (rhoBar 13040 BstLean.Part154.csC)) ≤ 0.000490418119 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000245201544 : ℝ) * 0.000980866300 := by gcongr
      _ ≤ (0.000490418119 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13040 BstLean.Part154.csC) * nuR (rhoBar 13040 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000980866300 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13040 BstLean.Part154.csC) * rhoBar 13040 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000245201544 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000245201544 / 2 + 0.399 * 0.000980866300 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000187286362 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000490418119 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119171603 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000245201544 / 1.414213562 := by gcongr
      _ ≤ (0.000069180087 : ℝ) := by norm_num

end BstLean.Part269.N13040

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13040
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13040 BstLean.Part154.csC) (piBar (rhoBar 13040 BstLean.Part154.csC)) ≤ 1.51478E-7 := by
  have hr0 : 0 ≤ rhoBar 13040 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13040 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13040 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13040 BstLean.Part154.csC) (piBar (rhoBar 13040 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13040 BstLean.Part154.csC) (piBar (rhoBar 13040 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13040 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000187286362 : ℝ) ^ 2 + 0.000119171603 ^ 2 + 3 * 0.000069180087 ^ 2 +
        2 * 0.797885 * 0.000187286362 * 0.000119171603 + 2 * 0.000187286362 * 0.000069180087 +
        4 * 0.797885 * 0.000119171603 * 0.000069180087 := by gcongr
    _ ≤ (1.51478E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13040 BstLean.Part154.csC Θ ≤ 0.002558397457 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13040 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13040 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13040 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13040 BstLean.Part154.csC) (piBar (rhoBar 13040 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13040 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035335220672 * 1.51478E-7 / (0.000245201164 : ℝ) := by gcongr
    _ ≤ 0.002558397457 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13040 BstLean.Part154.csC Θ ≤ 0.002837368885 + 0.000646464073 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13040 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13040 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13040 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035335220672 : ℝ) * ((2 * Θ * 0.000245201544 +
        (6863 / 10000) * 0.000245201544 * 13040 * 0.000980866300) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002837368885 + 0.000646464073 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13040 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13040 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13040 0.011 Θ ∧ gammaRatio 13040 0.011 Θ ≤ 0.000084293950 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13040 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035335220672 : ℝ) * 0.525 / ((1 - 0.011) * 13040) := by gcongr
      _ ≤ (0.000084293950 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13040 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13040 0.011 Θ) :=
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
    badAllowance 13040 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000383431726 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13040 BstLean.Part154.csC) 1.22 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 2 (rhoBar 13040 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13040 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13040 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13040 0.011 Θ) 1.12 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 1 (gammaRatio 13040 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13040 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13040 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13040 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13040 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035335220672 : ℝ) * 13040 *
        (1.3781E-8 / 1.1045361 + 1.6832E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000383431726 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13040 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003220800611 + 0.003204861530 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13040

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13040
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13040 BstLean.Part154.csC) (piBar (rhoBar 13040 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13040 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13040 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13040 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13040 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13040 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13040 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13040 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13040 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13040 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13040 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13040 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13040 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13040 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13040 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051788195208 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13040) ≤ 0.010458079479 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13040 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035335220672)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010458079479 + 2 * 0.737676 / 13040) := by gcongr
    _ ≤ (0.051788195208 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13040 12 ≤ 0.0015 := by
  exact BstLean.Part269.S27.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13040

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13040
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560518543197 : ℝ) ≤ plow 13040 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13040) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052409952915)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001343158665) : eMP 13040 0.011 xi bn ≤ 0.001156781910 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13040 : ℝ) * (1 - 0.011))) ≤ 0.000572007441 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001343158665 / (13040 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000572007441 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000572007441 : ℝ) + 3.141593 * 0.052409952915 / (13040 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001156781910 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052409952915)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001343158665) : PiBarMP 13040 12 0.011 xi bn ≤ 0.159114112235 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13040 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036649129117 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.563022150698 : ℝ) ≤ √((13040 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.192819388961 : ℝ) ≤ √(13040 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13040) ≤ 0.122007743896 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036649129117 + 0.052409952915 * 1.772454 / (2 * (113.563022150698 : ℝ))) * (1 + 0.001156781910) +
        8 / (13040 * 114.192819388961) + 0.122007743896 := by gcongr
    _ ≤ (0.159114112235 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052409952915)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001343158665) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280720396777) :
    parallelOracle 13040 0.011 xi bn cd ≤ 0.160078617259 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13040 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13040 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560518543197 : ℝ) ≤ plow 13040 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.192819388961 : ℝ) ≤ √(13040 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280720396777 : ℝ) / (2 * 0.560518543197 * 114.192819388961)) * 0.159114112235 +
        0.280720396777 ^ 2 / (2 * 0.560518543197 * 114.192819388961) := by gcongr
    _ ≤ (0.160078617259 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052409952915) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001343158665)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280720396777) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13040 13040 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560518543197 : ℝ) ≤ plow 13040 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.192819388961 : ℝ) ≤ √(13040 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13040 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13040 Θ 1.22 ≤ 0.011612818627 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.192819388961 := by gcongr <;> linarith
      _ ≤ (0.011612818627 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13040 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13040 13040 0.011 ≤ 0.008370814719 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13040 13040 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13040 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13040 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13040 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13040 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160078617259 + 0.011612818627 + (0.008370814719 : ℝ) *
        (1 + 2 * (0.280720396777 + 0.011612818627) / (0.560518543197 * 114.192819388961))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13040]

end BstLean.Part269.N13040

/-! The original eight local profiles supply actual 13040 moment certificates. -/
namespace BstLean.Part269.N13040
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13040 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13040 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13040 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052409952915 ∧
    0 ≤ bN 13040 BstLean.Part154.csC (groupTheta g) ∧ bN 13040 BstLean.Part154.csC (groupTheta g) ≤ 0.001343158665 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13040 13040 0.011
      (momentAllowance 13040 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13040 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13040 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13040 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13040 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13040 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228932201569 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13040 0.011
      (momentAllowance 13040 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13040 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13040
/-! The actual computed-centre upper energy formula at 13040. -/
namespace BstLean.Part269.N13040
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13040

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13040
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13040)
open BstLean.Part268 (cell13040)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084556008446
  | 2 => 0.085483321739
  | 3 => 0.086406639084
  | 4 => 0.087326876702
  | 5 => 0.088245157441
  | 6 => 0.089162843260
  | 7 => 0.090081571135
  | 8 => 0.091003292456
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13040 13040 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13040 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N13040

/-! Actual upper energy certificates on all 43 source endpoints at 13040. -/
namespace BstLean.Part269.N13040
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13040)
open BstLean.Part268 (cell13040)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13040 (gMinus 13040) (1 - (cell13040 i).lower) ≤ 1 ∧
    energyUpper 13040 (gMinus 13040) (BstLean.Part211.gPlus 13040)
      (finiteEnergy 13040 13040 0.011) (1 - (cell13040 i).lower) ≤
      (cell13040 i).energy := by
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
      have E := BstLean.Part269.S27.uniformEnergy10 (n := 13040) (by norm_num)
        (q := 1 - (cell13040 ⟨10,by decide⟩).lower)
        (by norm_num [cell13040]) (by norm_num [cell13040])
      exact ⟨E.1,E.2.trans (by norm_num [cell13040])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy11 (n := 13040) (by norm_num)
        (q := 1 - (cell13040 ⟨11,by decide⟩).lower)
        (by norm_num [cell13040]) (by norm_num [cell13040])
      exact ⟨E.1,E.2.trans (by norm_num [cell13040])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy12 (n := 13040) (by norm_num)
        (q := 1 - (cell13040 ⟨12,by decide⟩).lower)
        (by norm_num [cell13040]) (by norm_num [cell13040])
      exact ⟨E.1,E.2.trans (by norm_num [cell13040])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy13 (n := 13040) (by norm_num)
        (q := 1 - (cell13040 ⟨13,by decide⟩).lower)
        (by norm_num [cell13040]) (by norm_num [cell13040])
      exact ⟨E.1,E.2.trans (by norm_num [cell13040])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy14 (n := 13040) (by norm_num)
        (q := 1 - (cell13040 ⟨14,by decide⟩).lower)
        (by norm_num [cell13040]) (by norm_num [cell13040])
      exact ⟨E.1,E.2.trans (by norm_num [cell13040])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy15 (n := 13040) (by norm_num)
        (q := 1 - (cell13040 ⟨15,by decide⟩).lower)
        (by norm_num [cell13040]) (by norm_num [cell13040])
      exact ⟨E.1,E.2.trans (by norm_num [cell13040])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy16 (n := 13040) (by norm_num)
        (q := 1 - (cell13040 ⟨16,by decide⟩).lower)
        (by norm_num [cell13040]) (by norm_num [cell13040])
      exact ⟨E.1,E.2.trans (by norm_num [cell13040])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy17 (n := 13040) (by norm_num)
        (q := 1 - (cell13040 ⟨17,by decide⟩).lower)
        (by norm_num [cell13040]) (by norm_num [cell13040])
      exact ⟨E.1,E.2.trans (by norm_num [cell13040])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy18 (n := 13040) (by norm_num)
        (q := 1 - (cell13040 ⟨18,by decide⟩).lower)
        (by norm_num [cell13040]) (by norm_num [cell13040])
      exact ⟨E.1,E.2.trans (by norm_num [cell13040])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy19 (n := 13040) (by norm_num)
        (q := 1 - (cell13040 ⟨19,by decide⟩).lower)
        (by norm_num [cell13040]) (by norm_num [cell13040])
      exact ⟨E.1,E.2.trans (by norm_num [cell13040])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy20 (n := 13040) (by norm_num)
        (q := 1 - (cell13040 ⟨20,by decide⟩).lower)
        (by norm_num [cell13040]) (by norm_num [cell13040])
      exact ⟨E.1,E.2.trans (by norm_num [cell13040])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy21 (n := 13040) (by norm_num)
        (q := 1 - (cell13040 ⟨21,by decide⟩).lower)
        (by norm_num [cell13040]) (by norm_num [cell13040])
      exact ⟨E.1,E.2.trans (by norm_num [cell13040])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy22 (n := 13040) (by norm_num)
        (q := 1 - (cell13040 ⟨22,by decide⟩).lower)
        (by norm_num [cell13040]) (by norm_num [cell13040])
      exact ⟨E.1,E.2.trans (by norm_num [cell13040])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy23 (n := 13040) (by norm_num)
        (q := 1 - (cell13040 ⟨23,by decide⟩).lower)
        (by norm_num [cell13040]) (by norm_num [cell13040])
      exact ⟨E.1,E.2.trans (by norm_num [cell13040])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy24 (n := 13040) (by norm_num)
        (q := 1 - (cell13040 ⟨24,by decide⟩).lower)
        (by norm_num [cell13040]) (by norm_num [cell13040])
      exact ⟨E.1,E.2.trans (by norm_num [cell13040])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy25 (n := 13040) (by norm_num)
        (q := 1 - (cell13040 ⟨25,by decide⟩).lower)
        (by norm_num [cell13040]) (by norm_num [cell13040])
      exact ⟨E.1,E.2.trans (by norm_num [cell13040])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy26 (n := 13040) (by norm_num)
        (q := 1 - (cell13040 ⟨26,by decide⟩).lower)
        (by norm_num [cell13040]) (by norm_num [cell13040])
      exact ⟨E.1,E.2.trans (by norm_num [cell13040])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy27 (n := 13040) (by norm_num)
        (q := 1 - (cell13040 ⟨27,by decide⟩).lower)
        (by norm_num [cell13040]) (by norm_num [cell13040])
      exact ⟨E.1,E.2.trans (by norm_num [cell13040])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy28 (n := 13040) (by norm_num)
        (q := 1 - (cell13040 ⟨28,by decide⟩).lower)
        (by norm_num [cell13040]) (by norm_num [cell13040])
      exact ⟨E.1,E.2.trans (by norm_num [cell13040])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy29 (n := 13040) (by norm_num)
        (q := 1 - (cell13040 ⟨29,by decide⟩).lower)
        (by norm_num [cell13040]) (by norm_num [cell13040])
      exact ⟨E.1,E.2.trans (by norm_num [cell13040])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy30 (n := 13040) (by norm_num)
        (q := 1 - (cell13040 ⟨30,by decide⟩).lower)
        (by norm_num [cell13040]) (by norm_num [cell13040])
      exact ⟨E.1,E.2.trans (by norm_num [cell13040])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy31 (n := 13040) (by norm_num)
        (q := 1 - (cell13040 ⟨31,by decide⟩).lower)
        (by norm_num [cell13040]) (by norm_num [cell13040])
      exact ⟨E.1,E.2.trans (by norm_num [cell13040])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy32 (n := 13040) (by norm_num)
        (q := 1 - (cell13040 ⟨32,by decide⟩).lower)
        (by norm_num [cell13040]) (by norm_num [cell13040])
      exact ⟨E.1,E.2.trans (by norm_num [cell13040])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy33 (n := 13040) (by norm_num)
        (q := 1 - (cell13040 ⟨33,by decide⟩).lower)
        (by norm_num [cell13040]) (by norm_num [cell13040])
      exact ⟨E.1,E.2.trans (by norm_num [cell13040])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy34 (n := 13040) (by norm_num)
        (q := 1 - (cell13040 ⟨34,by decide⟩).lower)
        (by norm_num [cell13040]) (by norm_num [cell13040])
      exact ⟨E.1,E.2.trans (by norm_num [cell13040])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy35 (n := 13040) (by norm_num)
        (q := 1 - (cell13040 ⟨35,by decide⟩).lower)
        (by norm_num [cell13040]) (by norm_num [cell13040])
      exact ⟨E.1,E.2.trans (by norm_num [cell13040])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy36 (n := 13040) (by norm_num)
        (q := 1 - (cell13040 ⟨36,by decide⟩).lower)
        (by norm_num [cell13040]) (by norm_num [cell13040])
      exact ⟨E.1,E.2.trans (by norm_num [cell13040])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy37 (n := 13040) (by norm_num)
        (q := 1 - (cell13040 ⟨37,by decide⟩).lower)
        (by norm_num [cell13040]) (by norm_num [cell13040])
      exact ⟨E.1,E.2.trans (by norm_num [cell13040])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy38 (n := 13040) (by norm_num)
        (q := 1 - (cell13040 ⟨38,by decide⟩).lower)
        (by norm_num [cell13040]) (by norm_num [cell13040])
      exact ⟨E.1,E.2.trans (by norm_num [cell13040])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy39 (n := 13040) (by norm_num)
        (q := 1 - (cell13040 ⟨39,by decide⟩).lower)
        (by norm_num [cell13040]) (by norm_num [cell13040])
      exact ⟨E.1,E.2.trans (by norm_num [cell13040])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy40 (n := 13040) (by norm_num)
        (q := 1 - (cell13040 ⟨40,by decide⟩).lower)
        (by norm_num [cell13040]) (by norm_num [cell13040])
      exact ⟨E.1,E.2.trans (by norm_num [cell13040])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy41 (n := 13040) (by norm_num)
        (q := 1 - (cell13040 ⟨41,by decide⟩).lower)
        (by norm_num [cell13040]) (by norm_num [cell13040])
      exact ⟨E.1,E.2.trans (by norm_num [cell13040])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy42 (n := 13040) (by norm_num)
        (q := 1 - (cell13040 ⟨42,by decide⟩).lower)
        (by norm_num [cell13040]) (by norm_num [cell13040])
      exact ⟨E.1,E.2.trans (by norm_num [cell13040])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy43 (n := 13040) (by norm_num)
        (q := 1 - (cell13040 ⟨43,by decide⟩).lower)
        (by norm_num [cell13040]) (by norm_num [cell13040])
      exact ⟨E.1,E.2.trans (by norm_num [cell13040])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy44 (n := 13040) (by norm_num)
        (q := 1 - (cell13040 ⟨44,by decide⟩).lower)
        (by norm_num [cell13040]) (by norm_num [cell13040])
      exact ⟨E.1,E.2.trans (by norm_num [cell13040])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy45 (n := 13040) (by norm_num)
        (q := 1 - (cell13040 ⟨45,by decide⟩).lower)
        (by norm_num [cell13040]) (by norm_num [cell13040])
      exact ⟨E.1,E.2.trans (by norm_num [cell13040])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy46 (n := 13040) (by norm_num)
        (q := 1 - (cell13040 ⟨46,by decide⟩).lower)
        (by norm_num [cell13040]) (by norm_num [cell13040])
      exact ⟨E.1,E.2.trans (by norm_num [cell13040])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy47 (n := 13040) (by norm_num)
        (q := 1 - (cell13040 ⟨47,by decide⟩).lower)
        (by norm_num [cell13040]) (by norm_num [cell13040])
      exact ⟨E.1,E.2.trans (by norm_num [cell13040])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy48 (n := 13040) (by norm_num)
        (q := 1 - (cell13040 ⟨48,by decide⟩).lower)
        (by norm_num [cell13040]) (by norm_num [cell13040])
      exact ⟨E.1,E.2.trans (by norm_num [cell13040])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy49 (n := 13040) (by norm_num)
        (q := 1 - (cell13040 ⟨49,by decide⟩).lower)
        (by norm_num [cell13040]) (by norm_num [cell13040])
      exact ⟨E.1,E.2.trans (by norm_num [cell13040])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy50 (n := 13040) (by norm_num)
        (q := 1 - (cell13040 ⟨50,by decide⟩).lower)
        (by norm_num [cell13040]) (by norm_num [cell13040])
      exact ⟨E.1,E.2.trans (by norm_num [cell13040])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy51 (n := 13040) (by norm_num)
        (q := 1 - (cell13040 ⟨51,by decide⟩).lower)
        (by norm_num [cell13040]) (by norm_num [cell13040])
      exact ⟨E.1,E.2.trans (by norm_num [cell13040])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy52 (n := 13040) (by norm_num)
        (q := 1 - (cell13040 ⟨52,by decide⟩).lower)
        (by norm_num [cell13040]) (by norm_num [cell13040])
      exact ⟨E.1,E.2.trans (by norm_num [cell13040])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13040

/-! Source-cell containment and simple scalar guards at 13040. -/
namespace BstLean.Part269.N13040
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13040)
open BstLean.Part268 (cell13040)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13040 ⟨10,by decide⟩).lower ∧ (cell13040 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13040 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13040 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13040 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13040 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13040 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13040,cell13040,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13040 ⟨11,by decide⟩).lower ∧ (cell13040 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13040 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13040 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13040 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13040 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13040 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13040,cell13040,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13040 ⟨12,by decide⟩).lower ∧ (cell13040 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13040 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13040 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13040 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13040 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13040 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13040,cell13040,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13040 ⟨13,by decide⟩).lower ∧ (cell13040 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13040 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13040 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13040 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13040 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13040 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13040,cell13040,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13040 ⟨14,by decide⟩).lower ∧ (cell13040 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13040 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13040 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13040 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13040 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13040 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13040,cell13040,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13040 ⟨15,by decide⟩).lower ∧ (cell13040 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13040 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13040 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13040 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13040 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13040 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13040,cell13040,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13040 ⟨16,by decide⟩).lower ∧ (cell13040 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13040 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13040 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13040 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13040 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13040 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13040,cell13040,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13040 ⟨17,by decide⟩).lower ∧ (cell13040 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13040 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13040 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13040 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13040 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13040 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13040,cell13040,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13040 ⟨18,by decide⟩).lower ∧ (cell13040 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13040 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13040 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13040 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13040 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13040 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13040,cell13040,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13040 ⟨19,by decide⟩).lower ∧ (cell13040 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13040 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13040 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13040 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13040 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13040 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13040,cell13040,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13040 ⟨20,by decide⟩).lower ∧ (cell13040 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13040 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13040 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13040 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13040 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13040 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13040,cell13040,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13040 ⟨21,by decide⟩).lower ∧ (cell13040 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13040 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13040 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13040 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13040 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13040 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13040,cell13040,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13040 ⟨22,by decide⟩).lower ∧ (cell13040 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13040 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13040 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13040 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13040 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13040 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13040,cell13040,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13040 ⟨23,by decide⟩).lower ∧ (cell13040 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13040 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13040 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13040 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13040 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13040 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13040,cell13040,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13040 ⟨24,by decide⟩).lower ∧ (cell13040 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13040 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13040 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13040 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13040 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13040 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13040,cell13040,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13040 ⟨25,by decide⟩).lower ∧ (cell13040 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13040 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13040 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13040 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13040 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13040 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13040,cell13040,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13040 ⟨26,by decide⟩).lower ∧ (cell13040 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13040 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13040 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13040 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13040 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13040 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13040,cell13040,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13040 ⟨27,by decide⟩).lower ∧ (cell13040 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13040 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13040 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13040 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13040 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13040 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13040,cell13040,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13040 ⟨28,by decide⟩).lower ∧ (cell13040 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13040 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13040 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13040 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13040 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13040 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13040,cell13040,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13040 ⟨29,by decide⟩).lower ∧ (cell13040 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13040 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13040 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13040 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13040 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13040 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13040,cell13040,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13040 ⟨30,by decide⟩).lower ∧ (cell13040 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13040 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13040 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13040 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13040 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13040 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13040,cell13040,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13040 ⟨31,by decide⟩).lower ∧ (cell13040 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13040 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13040 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13040 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13040 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13040 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13040,cell13040,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13040 ⟨32,by decide⟩).lower ∧ (cell13040 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13040 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13040 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13040 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13040 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13040 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13040,cell13040,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13040 ⟨33,by decide⟩).lower ∧ (cell13040 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13040 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13040 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13040 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13040 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13040 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13040,cell13040,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13040 ⟨34,by decide⟩).lower ∧ (cell13040 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13040 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13040 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13040 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13040 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13040 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13040,cell13040,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13040 ⟨35,by decide⟩).lower ∧ (cell13040 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13040 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13040 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13040 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13040 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13040 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13040,cell13040,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13040 ⟨36,by decide⟩).lower ∧ (cell13040 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13040 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13040 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13040 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13040 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13040 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13040,cell13040,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13040 ⟨37,by decide⟩).lower ∧ (cell13040 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13040 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13040 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13040 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13040 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13040 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13040,cell13040,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13040 ⟨38,by decide⟩).lower ∧ (cell13040 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13040 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13040 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13040 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13040 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13040 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13040,cell13040,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13040 ⟨39,by decide⟩).lower ∧ (cell13040 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13040 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13040 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13040 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13040 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13040 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13040,cell13040,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13040 ⟨40,by decide⟩).lower ∧ (cell13040 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13040 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13040 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13040 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13040 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13040 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13040,cell13040,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13040 ⟨41,by decide⟩).lower ∧ (cell13040 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13040 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13040 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13040 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13040 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13040 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13040,cell13040,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13040 ⟨42,by decide⟩).lower ∧ (cell13040 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13040 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13040 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13040 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13040 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13040 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13040,cell13040,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13040 ⟨43,by decide⟩).lower ∧ (cell13040 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13040 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13040 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13040 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13040 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13040 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13040,cell13040,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13040 ⟨44,by decide⟩).lower ∧ (cell13040 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13040 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13040 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13040 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13040 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13040 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13040,cell13040,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13040 ⟨45,by decide⟩).lower ∧ (cell13040 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13040 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13040 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13040 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13040 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13040 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13040,cell13040,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13040 ⟨46,by decide⟩).lower ∧ (cell13040 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13040 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13040 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13040 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13040 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13040 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13040,cell13040,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13040 ⟨47,by decide⟩).lower ∧ (cell13040 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13040 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13040 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13040 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13040 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13040 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13040,cell13040,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13040 ⟨48,by decide⟩).lower ∧ (cell13040 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13040 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13040 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13040 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13040 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13040 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13040,cell13040,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13040 ⟨49,by decide⟩).lower ∧ (cell13040 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13040 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13040 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13040 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13040 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13040 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13040,cell13040,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13040 ⟨50,by decide⟩).lower ∧ (cell13040 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13040 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13040 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13040 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13040 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13040 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13040,cell13040,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13040 ⟨51,by decide⟩).lower ∧ (cell13040 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13040 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13040 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13040 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13040 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13040 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13040,cell13040,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13040 ⟨52,by decide⟩).lower ∧ (cell13040 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13040 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13040 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13040 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13040 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13040 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13040,cell13040,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13040 i).lower ∧
    (cell13040 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13040 i).upper ≤ (0.532 : ℝ) ∧
    (cell13040 i).centre ≤ (0.1 : ℝ) ∧ (cell13040 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13040 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13040 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13040

/-! The local source numeric instances at 13040 have no network premises. -/
namespace BstLean.Part269.N13040
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13040)
open BstLean.Part268 (cell13040)

noncomputable def sourceNumerics13040 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13040 (cell13040 i)
      scalarRow13040.M scalarRow13040.H scalarRow13040.xi := by
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
    energy_allowance := scalarRow13040.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13040]
    centre_nonneg := (scalarRow13040.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D27.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13040])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13040
/-! Actual 13041 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13041
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13041 ≤ (1.035333854111 : ℝ) := by
  have hr : (114.197197864045 : ℝ) ≤ √(13041 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.197197864045 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13041 13041 (11 / 1000) ≤
    (0.008370493768 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13041) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.197197864045 : ℝ) ≤ √(13041 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13041)
  have hdiv : K / √(13041 : ℝ) ≤ K / 114.197197864045 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.197197864045 ≤ (0.008370493768 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13041.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13041 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13041 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13041 := gPlus_lower 13041
end BstLean.Part269.N13041

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13041
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035333854110 : ℝ) ≤ wn 13041 := by
  have hn : √(13041 : ℝ) ≤ 114.197197864046 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13041 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.197197864046 ≤ 2 / √(13041 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000245182038 : ℝ) ≤ rhoBar 13041 BstLean.Part154.csC ∧
    rhoBar 13041 BstLean.Part154.csC ≤ 0.000245182418 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035333854110 : ℝ) / (1.295212 * 13041) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035333854111 : ℝ) / (1.29521 * 13041) := by gcongr
      _ ≤ (0.000245182418 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13041 BstLean.Part154.csC) ≤ 0.000980789787 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13041 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13041 BstLean.Part154.csC) (piBar (rhoBar 13041 BstLean.Part154.csC)) ≤ 0.000187271753 ∧
    cc1 (rhoBar 13041 BstLean.Part154.csC) (piBar (rhoBar 13041 BstLean.Part154.csC)) ≤ 0.000119162308 ∧
    cc2 (rhoBar 13041 BstLean.Part154.csC) ≤ 0.000069174691 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13041 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13041 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13041 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13041 BstLean.Part154.csC * nuR (rhoBar 13041 BstLean.Part154.csC)) ≤ 0.000490379865 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000245182418 : ℝ) * 0.000980789787 := by gcongr
      _ ≤ (0.000490379865 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13041 BstLean.Part154.csC) * nuR (rhoBar 13041 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000980789787 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13041 BstLean.Part154.csC) * rhoBar 13041 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000245182418 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000245182418 / 2 + 0.399 * 0.000980789787 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000187271753 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000490379865 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119162308 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000245182418 / 1.414213562 := by gcongr
      _ ≤ (0.000069174691 : ℝ) := by norm_num

end BstLean.Part269.N13041

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13041
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13041 BstLean.Part154.csC) (piBar (rhoBar 13041 BstLean.Part154.csC)) ≤ 1.51454E-7 := by
  have hr0 : 0 ≤ rhoBar 13041 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13041 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13041 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13041 BstLean.Part154.csC) (piBar (rhoBar 13041 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13041 BstLean.Part154.csC) (piBar (rhoBar 13041 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13041 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000187271753 : ℝ) ^ 2 + 0.000119162308 ^ 2 + 3 * 0.000069174691 ^ 2 +
        2 * 0.797885 * 0.000187271753 * 0.000119162308 + 2 * 0.000187271753 * 0.000069174691 +
        4 * 0.797885 * 0.000119162308 * 0.000069174691 := by gcongr
    _ ≤ (1.51454E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13041 BstLean.Part154.csC Θ ≤ 0.002558188273 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13041 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13041 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13041 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13041 BstLean.Part154.csC) (piBar (rhoBar 13041 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13041 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035333854111 * 1.51454E-7 / (0.000245182038 : ℝ) := by gcongr
    _ ≤ 0.002558188273 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13041 BstLean.Part154.csC Θ ≤ 0.002837140064 + 0.000646412794 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13041 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13041 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13041 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035333854111 : ℝ) * ((2 * Θ * 0.000245182418 +
        (6863 / 10000) * 0.000245182418 * 13041 * 0.000980789787) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002837140064 + 0.000646412794 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13041 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13041 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13041 0.011 Θ ∧ gammaRatio 13041 0.011 Θ ≤ 0.000084287375 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13041 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035333854111 : ℝ) * 0.525 / ((1 - 0.011) * 13041) := by gcongr
      _ ≤ (0.000084287375 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13041 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13041 0.011 Θ) :=
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
    badAllowance 13041 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000383431726 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13041 BstLean.Part154.csC) 1.22 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 2 (rhoBar 13041 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13041 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13041 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13041 0.011 Θ) 1.12 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 1 (gammaRatio 13041 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13041 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13041 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13041 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13041 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035333854111 : ℝ) * 13041 *
        (1.3781E-8 / 1.1045361 + 1.6832E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000383431726 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13041 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003220571790 + 0.003204601067 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13041

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13041
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13041 BstLean.Part154.csC) (piBar (rhoBar 13041 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13041 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13041 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13041 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13041 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13041 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13041 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13041 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13041 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13041 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13041 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13041 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13041 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13041 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13041 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051786188327 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13041) ≤ 0.010457678502 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13041 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035333854111)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010457678502 + 2 * 0.737676 / 13041) := by gcongr
    _ ≤ (0.051786188327 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13041 12 ≤ 0.0015 := by
  exact BstLean.Part269.S27.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13041

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13041
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560518586090 : ℝ) ≤ plow 13041 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13041) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052409587351)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001343048844) : eMP 13041 0.011 xi bn ≤ 0.001156690210 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13041 : ℝ) * (1 - 0.011))) ≤ 0.000571962125 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001343048844 / (13041 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000571962125 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000571962125 : ℝ) + 3.141593 * 0.052409587351 / (13041 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001156690210 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052409587351)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001343048844) : PiBarMP 13041 12 0.011 xi bn ≤ 0.159107911682 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13041 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036647630811 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.567376477578 : ℝ) ≤ √((13041 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.197197864045 : ℝ) ≤ √(13041 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13041) ≤ 0.122003065954 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036647630811 + 0.052409587351 * 1.772454 / (2 * (113.567376477578 : ℝ))) * (1 + 0.001156690210) +
        8 / (13041 * 114.197197864045) + 0.122003065954 := by gcongr
    _ ≤ (0.159107911682 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052409587351)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001343048844) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280717591484) :
    parallelOracle 13041 0.011 xi bn cd ≤ 0.160072350266 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13041 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13041 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560518586090 : ℝ) ≤ plow 13041 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.197197864045 : ℝ) ≤ √(13041 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280717591484 : ℝ) / (2 * 0.560518586090 * 114.197197864045)) * 0.159107911682 +
        0.280717591484 ^ 2 / (2 * 0.560518586090 * 114.197197864045) := by gcongr
    _ ≤ (0.160072350266 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052409587351) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001343048844)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280717591484) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13041 13041 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560518586090 : ℝ) ≤ plow 13041 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.197197864045 : ℝ) ≤ √(13041 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13041 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13041 Θ 1.22 ≤ 0.011612373376 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.197197864045 := by gcongr <;> linarith
      _ ≤ (0.011612373376 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13041 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13041 13041 0.011 ≤ 0.008370493768 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13041 13041 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13041 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13041 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13041 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13041 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160072350266 + 0.011612373376 + (0.008370493768 : ℝ) *
        (1 + 2 * (0.280717591484 + 0.011612373376) / (0.560518586090 * 114.197197864045))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13041]

end BstLean.Part269.N13041

/-! The original eight local profiles supply actual 13041 moment certificates. -/
namespace BstLean.Part269.N13041
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13041 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13041 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13041 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052409587351 ∧
    0 ≤ bN 13041 BstLean.Part154.csC (groupTheta g) ∧ bN 13041 BstLean.Part154.csC (groupTheta g) ≤ 0.001343048844 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13041 13041 0.011
      (momentAllowance 13041 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13041 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13041 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13041 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13041 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13041 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228931403157 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13041 0.011
      (momentAllowance 13041 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13041 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13041
/-! The actual computed-centre upper energy formula at 13041. -/
namespace BstLean.Part269.N13041
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13041

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13041
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13041)
open BstLean.Part268 (cell13041)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084553421936
  | 2 => 0.085480701793
  | 3 => 0.086403980714
  | 4 => 0.087324173745
  | 5 => 0.088242402343
  | 6 => 0.089160026835
  | 7 => 0.090078682285
  | 8 => 0.091000317867
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13041 13041 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13041 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N13041

/-! Actual upper energy certificates on all 43 source endpoints at 13041. -/
namespace BstLean.Part269.N13041
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13041)
open BstLean.Part268 (cell13041)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13041 (gMinus 13041) (1 - (cell13041 i).lower) ≤ 1 ∧
    energyUpper 13041 (gMinus 13041) (BstLean.Part211.gPlus 13041)
      (finiteEnergy 13041 13041 0.011) (1 - (cell13041 i).lower) ≤
      (cell13041 i).energy := by
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
      have E := BstLean.Part269.S27.uniformEnergy10 (n := 13041) (by norm_num)
        (q := 1 - (cell13041 ⟨10,by decide⟩).lower)
        (by norm_num [cell13041]) (by norm_num [cell13041])
      exact ⟨E.1,E.2.trans (by norm_num [cell13041])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy11 (n := 13041) (by norm_num)
        (q := 1 - (cell13041 ⟨11,by decide⟩).lower)
        (by norm_num [cell13041]) (by norm_num [cell13041])
      exact ⟨E.1,E.2.trans (by norm_num [cell13041])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy12 (n := 13041) (by norm_num)
        (q := 1 - (cell13041 ⟨12,by decide⟩).lower)
        (by norm_num [cell13041]) (by norm_num [cell13041])
      exact ⟨E.1,E.2.trans (by norm_num [cell13041])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy13 (n := 13041) (by norm_num)
        (q := 1 - (cell13041 ⟨13,by decide⟩).lower)
        (by norm_num [cell13041]) (by norm_num [cell13041])
      exact ⟨E.1,E.2.trans (by norm_num [cell13041])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy14 (n := 13041) (by norm_num)
        (q := 1 - (cell13041 ⟨14,by decide⟩).lower)
        (by norm_num [cell13041]) (by norm_num [cell13041])
      exact ⟨E.1,E.2.trans (by norm_num [cell13041])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy15 (n := 13041) (by norm_num)
        (q := 1 - (cell13041 ⟨15,by decide⟩).lower)
        (by norm_num [cell13041]) (by norm_num [cell13041])
      exact ⟨E.1,E.2.trans (by norm_num [cell13041])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy16 (n := 13041) (by norm_num)
        (q := 1 - (cell13041 ⟨16,by decide⟩).lower)
        (by norm_num [cell13041]) (by norm_num [cell13041])
      exact ⟨E.1,E.2.trans (by norm_num [cell13041])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy17 (n := 13041) (by norm_num)
        (q := 1 - (cell13041 ⟨17,by decide⟩).lower)
        (by norm_num [cell13041]) (by norm_num [cell13041])
      exact ⟨E.1,E.2.trans (by norm_num [cell13041])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy18 (n := 13041) (by norm_num)
        (q := 1 - (cell13041 ⟨18,by decide⟩).lower)
        (by norm_num [cell13041]) (by norm_num [cell13041])
      exact ⟨E.1,E.2.trans (by norm_num [cell13041])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy19 (n := 13041) (by norm_num)
        (q := 1 - (cell13041 ⟨19,by decide⟩).lower)
        (by norm_num [cell13041]) (by norm_num [cell13041])
      exact ⟨E.1,E.2.trans (by norm_num [cell13041])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy20 (n := 13041) (by norm_num)
        (q := 1 - (cell13041 ⟨20,by decide⟩).lower)
        (by norm_num [cell13041]) (by norm_num [cell13041])
      exact ⟨E.1,E.2.trans (by norm_num [cell13041])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy21 (n := 13041) (by norm_num)
        (q := 1 - (cell13041 ⟨21,by decide⟩).lower)
        (by norm_num [cell13041]) (by norm_num [cell13041])
      exact ⟨E.1,E.2.trans (by norm_num [cell13041])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy22 (n := 13041) (by norm_num)
        (q := 1 - (cell13041 ⟨22,by decide⟩).lower)
        (by norm_num [cell13041]) (by norm_num [cell13041])
      exact ⟨E.1,E.2.trans (by norm_num [cell13041])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy23 (n := 13041) (by norm_num)
        (q := 1 - (cell13041 ⟨23,by decide⟩).lower)
        (by norm_num [cell13041]) (by norm_num [cell13041])
      exact ⟨E.1,E.2.trans (by norm_num [cell13041])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy24 (n := 13041) (by norm_num)
        (q := 1 - (cell13041 ⟨24,by decide⟩).lower)
        (by norm_num [cell13041]) (by norm_num [cell13041])
      exact ⟨E.1,E.2.trans (by norm_num [cell13041])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy25 (n := 13041) (by norm_num)
        (q := 1 - (cell13041 ⟨25,by decide⟩).lower)
        (by norm_num [cell13041]) (by norm_num [cell13041])
      exact ⟨E.1,E.2.trans (by norm_num [cell13041])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy26 (n := 13041) (by norm_num)
        (q := 1 - (cell13041 ⟨26,by decide⟩).lower)
        (by norm_num [cell13041]) (by norm_num [cell13041])
      exact ⟨E.1,E.2.trans (by norm_num [cell13041])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy27 (n := 13041) (by norm_num)
        (q := 1 - (cell13041 ⟨27,by decide⟩).lower)
        (by norm_num [cell13041]) (by norm_num [cell13041])
      exact ⟨E.1,E.2.trans (by norm_num [cell13041])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy28 (n := 13041) (by norm_num)
        (q := 1 - (cell13041 ⟨28,by decide⟩).lower)
        (by norm_num [cell13041]) (by norm_num [cell13041])
      exact ⟨E.1,E.2.trans (by norm_num [cell13041])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy29 (n := 13041) (by norm_num)
        (q := 1 - (cell13041 ⟨29,by decide⟩).lower)
        (by norm_num [cell13041]) (by norm_num [cell13041])
      exact ⟨E.1,E.2.trans (by norm_num [cell13041])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy30 (n := 13041) (by norm_num)
        (q := 1 - (cell13041 ⟨30,by decide⟩).lower)
        (by norm_num [cell13041]) (by norm_num [cell13041])
      exact ⟨E.1,E.2.trans (by norm_num [cell13041])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy31 (n := 13041) (by norm_num)
        (q := 1 - (cell13041 ⟨31,by decide⟩).lower)
        (by norm_num [cell13041]) (by norm_num [cell13041])
      exact ⟨E.1,E.2.trans (by norm_num [cell13041])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy32 (n := 13041) (by norm_num)
        (q := 1 - (cell13041 ⟨32,by decide⟩).lower)
        (by norm_num [cell13041]) (by norm_num [cell13041])
      exact ⟨E.1,E.2.trans (by norm_num [cell13041])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy33 (n := 13041) (by norm_num)
        (q := 1 - (cell13041 ⟨33,by decide⟩).lower)
        (by norm_num [cell13041]) (by norm_num [cell13041])
      exact ⟨E.1,E.2.trans (by norm_num [cell13041])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy34 (n := 13041) (by norm_num)
        (q := 1 - (cell13041 ⟨34,by decide⟩).lower)
        (by norm_num [cell13041]) (by norm_num [cell13041])
      exact ⟨E.1,E.2.trans (by norm_num [cell13041])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy35 (n := 13041) (by norm_num)
        (q := 1 - (cell13041 ⟨35,by decide⟩).lower)
        (by norm_num [cell13041]) (by norm_num [cell13041])
      exact ⟨E.1,E.2.trans (by norm_num [cell13041])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy36 (n := 13041) (by norm_num)
        (q := 1 - (cell13041 ⟨36,by decide⟩).lower)
        (by norm_num [cell13041]) (by norm_num [cell13041])
      exact ⟨E.1,E.2.trans (by norm_num [cell13041])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy37 (n := 13041) (by norm_num)
        (q := 1 - (cell13041 ⟨37,by decide⟩).lower)
        (by norm_num [cell13041]) (by norm_num [cell13041])
      exact ⟨E.1,E.2.trans (by norm_num [cell13041])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy38 (n := 13041) (by norm_num)
        (q := 1 - (cell13041 ⟨38,by decide⟩).lower)
        (by norm_num [cell13041]) (by norm_num [cell13041])
      exact ⟨E.1,E.2.trans (by norm_num [cell13041])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy39 (n := 13041) (by norm_num)
        (q := 1 - (cell13041 ⟨39,by decide⟩).lower)
        (by norm_num [cell13041]) (by norm_num [cell13041])
      exact ⟨E.1,E.2.trans (by norm_num [cell13041])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy40 (n := 13041) (by norm_num)
        (q := 1 - (cell13041 ⟨40,by decide⟩).lower)
        (by norm_num [cell13041]) (by norm_num [cell13041])
      exact ⟨E.1,E.2.trans (by norm_num [cell13041])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy41 (n := 13041) (by norm_num)
        (q := 1 - (cell13041 ⟨41,by decide⟩).lower)
        (by norm_num [cell13041]) (by norm_num [cell13041])
      exact ⟨E.1,E.2.trans (by norm_num [cell13041])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy42 (n := 13041) (by norm_num)
        (q := 1 - (cell13041 ⟨42,by decide⟩).lower)
        (by norm_num [cell13041]) (by norm_num [cell13041])
      exact ⟨E.1,E.2.trans (by norm_num [cell13041])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy43 (n := 13041) (by norm_num)
        (q := 1 - (cell13041 ⟨43,by decide⟩).lower)
        (by norm_num [cell13041]) (by norm_num [cell13041])
      exact ⟨E.1,E.2.trans (by norm_num [cell13041])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy44 (n := 13041) (by norm_num)
        (q := 1 - (cell13041 ⟨44,by decide⟩).lower)
        (by norm_num [cell13041]) (by norm_num [cell13041])
      exact ⟨E.1,E.2.trans (by norm_num [cell13041])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy45 (n := 13041) (by norm_num)
        (q := 1 - (cell13041 ⟨45,by decide⟩).lower)
        (by norm_num [cell13041]) (by norm_num [cell13041])
      exact ⟨E.1,E.2.trans (by norm_num [cell13041])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy46 (n := 13041) (by norm_num)
        (q := 1 - (cell13041 ⟨46,by decide⟩).lower)
        (by norm_num [cell13041]) (by norm_num [cell13041])
      exact ⟨E.1,E.2.trans (by norm_num [cell13041])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy47 (n := 13041) (by norm_num)
        (q := 1 - (cell13041 ⟨47,by decide⟩).lower)
        (by norm_num [cell13041]) (by norm_num [cell13041])
      exact ⟨E.1,E.2.trans (by norm_num [cell13041])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy48 (n := 13041) (by norm_num)
        (q := 1 - (cell13041 ⟨48,by decide⟩).lower)
        (by norm_num [cell13041]) (by norm_num [cell13041])
      exact ⟨E.1,E.2.trans (by norm_num [cell13041])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy49 (n := 13041) (by norm_num)
        (q := 1 - (cell13041 ⟨49,by decide⟩).lower)
        (by norm_num [cell13041]) (by norm_num [cell13041])
      exact ⟨E.1,E.2.trans (by norm_num [cell13041])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy50 (n := 13041) (by norm_num)
        (q := 1 - (cell13041 ⟨50,by decide⟩).lower)
        (by norm_num [cell13041]) (by norm_num [cell13041])
      exact ⟨E.1,E.2.trans (by norm_num [cell13041])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy51 (n := 13041) (by norm_num)
        (q := 1 - (cell13041 ⟨51,by decide⟩).lower)
        (by norm_num [cell13041]) (by norm_num [cell13041])
      exact ⟨E.1,E.2.trans (by norm_num [cell13041])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy52 (n := 13041) (by norm_num)
        (q := 1 - (cell13041 ⟨52,by decide⟩).lower)
        (by norm_num [cell13041]) (by norm_num [cell13041])
      exact ⟨E.1,E.2.trans (by norm_num [cell13041])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13041

/-! Source-cell containment and simple scalar guards at 13041. -/
namespace BstLean.Part269.N13041
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13041)
open BstLean.Part268 (cell13041)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13041 ⟨10,by decide⟩).lower ∧ (cell13041 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13041 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13041 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13041 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13041 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13041 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13041,cell13041,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13041 ⟨11,by decide⟩).lower ∧ (cell13041 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13041 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13041 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13041 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13041 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13041 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13041,cell13041,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13041 ⟨12,by decide⟩).lower ∧ (cell13041 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13041 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13041 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13041 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13041 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13041 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13041,cell13041,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13041 ⟨13,by decide⟩).lower ∧ (cell13041 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13041 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13041 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13041 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13041 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13041 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13041,cell13041,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13041 ⟨14,by decide⟩).lower ∧ (cell13041 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13041 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13041 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13041 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13041 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13041 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13041,cell13041,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13041 ⟨15,by decide⟩).lower ∧ (cell13041 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13041 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13041 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13041 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13041 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13041 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13041,cell13041,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13041 ⟨16,by decide⟩).lower ∧ (cell13041 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13041 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13041 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13041 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13041 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13041 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13041,cell13041,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13041 ⟨17,by decide⟩).lower ∧ (cell13041 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13041 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13041 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13041 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13041 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13041 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13041,cell13041,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13041 ⟨18,by decide⟩).lower ∧ (cell13041 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13041 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13041 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13041 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13041 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13041 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13041,cell13041,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13041 ⟨19,by decide⟩).lower ∧ (cell13041 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13041 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13041 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13041 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13041 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13041 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13041,cell13041,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13041 ⟨20,by decide⟩).lower ∧ (cell13041 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13041 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13041 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13041 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13041 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13041 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13041,cell13041,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13041 ⟨21,by decide⟩).lower ∧ (cell13041 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13041 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13041 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13041 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13041 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13041 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13041,cell13041,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13041 ⟨22,by decide⟩).lower ∧ (cell13041 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13041 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13041 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13041 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13041 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13041 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13041,cell13041,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13041 ⟨23,by decide⟩).lower ∧ (cell13041 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13041 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13041 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13041 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13041 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13041 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13041,cell13041,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13041 ⟨24,by decide⟩).lower ∧ (cell13041 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13041 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13041 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13041 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13041 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13041 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13041,cell13041,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13041 ⟨25,by decide⟩).lower ∧ (cell13041 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13041 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13041 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13041 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13041 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13041 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13041,cell13041,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13041 ⟨26,by decide⟩).lower ∧ (cell13041 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13041 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13041 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13041 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13041 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13041 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13041,cell13041,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13041 ⟨27,by decide⟩).lower ∧ (cell13041 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13041 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13041 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13041 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13041 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13041 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13041,cell13041,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13041 ⟨28,by decide⟩).lower ∧ (cell13041 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13041 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13041 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13041 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13041 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13041 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13041,cell13041,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13041 ⟨29,by decide⟩).lower ∧ (cell13041 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13041 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13041 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13041 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13041 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13041 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13041,cell13041,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13041 ⟨30,by decide⟩).lower ∧ (cell13041 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13041 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13041 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13041 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13041 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13041 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13041,cell13041,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13041 ⟨31,by decide⟩).lower ∧ (cell13041 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13041 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13041 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13041 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13041 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13041 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13041,cell13041,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13041 ⟨32,by decide⟩).lower ∧ (cell13041 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13041 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13041 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13041 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13041 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13041 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13041,cell13041,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13041 ⟨33,by decide⟩).lower ∧ (cell13041 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13041 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13041 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13041 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13041 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13041 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13041,cell13041,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13041 ⟨34,by decide⟩).lower ∧ (cell13041 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13041 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13041 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13041 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13041 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13041 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13041,cell13041,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13041 ⟨35,by decide⟩).lower ∧ (cell13041 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13041 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13041 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13041 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13041 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13041 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13041,cell13041,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13041 ⟨36,by decide⟩).lower ∧ (cell13041 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13041 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13041 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13041 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13041 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13041 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13041,cell13041,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13041 ⟨37,by decide⟩).lower ∧ (cell13041 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13041 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13041 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13041 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13041 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13041 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13041,cell13041,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13041 ⟨38,by decide⟩).lower ∧ (cell13041 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13041 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13041 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13041 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13041 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13041 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13041,cell13041,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13041 ⟨39,by decide⟩).lower ∧ (cell13041 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13041 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13041 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13041 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13041 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13041 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13041,cell13041,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13041 ⟨40,by decide⟩).lower ∧ (cell13041 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13041 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13041 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13041 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13041 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13041 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13041,cell13041,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13041 ⟨41,by decide⟩).lower ∧ (cell13041 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13041 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13041 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13041 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13041 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13041 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13041,cell13041,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13041 ⟨42,by decide⟩).lower ∧ (cell13041 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13041 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13041 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13041 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13041 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13041 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13041,cell13041,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13041 ⟨43,by decide⟩).lower ∧ (cell13041 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13041 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13041 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13041 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13041 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13041 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13041,cell13041,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13041 ⟨44,by decide⟩).lower ∧ (cell13041 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13041 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13041 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13041 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13041 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13041 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13041,cell13041,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13041 ⟨45,by decide⟩).lower ∧ (cell13041 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13041 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13041 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13041 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13041 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13041 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13041,cell13041,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13041 ⟨46,by decide⟩).lower ∧ (cell13041 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13041 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13041 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13041 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13041 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13041 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13041,cell13041,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13041 ⟨47,by decide⟩).lower ∧ (cell13041 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13041 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13041 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13041 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13041 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13041 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13041,cell13041,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13041 ⟨48,by decide⟩).lower ∧ (cell13041 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13041 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13041 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13041 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13041 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13041 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13041,cell13041,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13041 ⟨49,by decide⟩).lower ∧ (cell13041 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13041 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13041 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13041 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13041 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13041 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13041,cell13041,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13041 ⟨50,by decide⟩).lower ∧ (cell13041 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13041 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13041 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13041 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13041 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13041 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13041,cell13041,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13041 ⟨51,by decide⟩).lower ∧ (cell13041 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13041 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13041 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13041 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13041 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13041 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13041,cell13041,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13041 ⟨52,by decide⟩).lower ∧ (cell13041 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13041 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13041 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13041 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13041 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13041 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13041,cell13041,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13041 i).lower ∧
    (cell13041 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13041 i).upper ≤ (0.532 : ℝ) ∧
    (cell13041 i).centre ≤ (0.1 : ℝ) ∧ (cell13041 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13041 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13041 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13041

/-! The local source numeric instances at 13041 have no network premises. -/
namespace BstLean.Part269.N13041
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13041)
open BstLean.Part268 (cell13041)

noncomputable def sourceNumerics13041 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13041 (cell13041 i)
      scalarRow13041.M scalarRow13041.H scalarRow13041.xi := by
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
    energy_allowance := scalarRow13041.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13041]
    centre_nonneg := (scalarRow13041.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D27.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13041])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13041
/-! Actual 13042 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13042
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13042 ≤ (1.035332487708 : ℝ) := by
  have hr : (114.201576171259 : ℝ) ≤ √(13042 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.201576171259 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13042 13042 (11 / 1000) ≤
    (0.008370172854 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13042) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.201576171259 : ℝ) ≤ √(13042 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13042)
  have hdiv : K / √(13042 : ℝ) ≤ K / 114.201576171259 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.201576171259 ≤ (0.008370172854 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13042.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13042 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13042 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13042 := gPlus_lower 13042
end BstLean.Part269.N13042

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13042
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035332487707 : ℝ) ≤ wn 13042 := by
  have hn : √(13042 : ℝ) ≤ 114.201576171260 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13042 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.201576171260 ≤ 2 / √(13042 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000245162915 : ℝ) ≤ rhoBar 13042 BstLean.Part154.csC ∧
    rhoBar 13042 BstLean.Part154.csC ≤ 0.000245163295 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035332487707 : ℝ) / (1.295212 * 13042) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035332487708 : ℝ) / (1.29521 * 13042) := by gcongr
      _ ≤ (0.000245163295 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13042 BstLean.Part154.csC) ≤ 0.000980713286 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13042 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13042 BstLean.Part154.csC) (piBar (rhoBar 13042 BstLean.Part154.csC)) ≤ 0.000187257146 ∧
    cc1 (rhoBar 13042 BstLean.Part154.csC) (piBar (rhoBar 13042 BstLean.Part154.csC)) ≤ 0.000119153013 ∧
    cc2 (rhoBar 13042 BstLean.Part154.csC) ≤ 0.000069169295 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13042 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13042 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13042 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13042 BstLean.Part154.csC * nuR (rhoBar 13042 BstLean.Part154.csC)) ≤ 0.000490341617 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000245163295 : ℝ) * 0.000980713286 := by gcongr
      _ ≤ (0.000490341617 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13042 BstLean.Part154.csC) * nuR (rhoBar 13042 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000980713286 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13042 BstLean.Part154.csC) * rhoBar 13042 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000245163295 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000245163295 / 2 + 0.399 * 0.000980713286 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000187257146 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000490341617 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119153013 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000245163295 / 1.414213562 := by gcongr
      _ ≤ (0.000069169295 : ℝ) := by norm_num

end BstLean.Part269.N13042

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13042
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13042 BstLean.Part154.csC) (piBar (rhoBar 13042 BstLean.Part154.csC)) ≤ 1.51430E-7 := by
  have hr0 : 0 ≤ rhoBar 13042 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13042 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13042 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13042 BstLean.Part154.csC) (piBar (rhoBar 13042 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13042 BstLean.Part154.csC) (piBar (rhoBar 13042 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13042 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000187257146 : ℝ) ^ 2 + 0.000119153013 ^ 2 + 3 * 0.000069169295 ^ 2 +
        2 * 0.797885 * 0.000187257146 * 0.000119153013 + 2 * 0.000187257146 * 0.000069169295 +
        4 * 0.797885 * 0.000119153013 * 0.000069169295 := by gcongr
    _ ≤ (1.51430E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13042 BstLean.Part154.csC Θ ≤ 0.002557979026 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13042 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13042 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13042 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13042 BstLean.Part154.csC) (piBar (rhoBar 13042 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13042 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035332487708 * 1.51430E-7 / (0.000245162915 : ℝ) := by gcongr
    _ ≤ 0.002557979026 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13042 BstLean.Part154.csC Θ ≤ 0.002836911281 + 0.000646361524 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13042 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13042 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13042 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035332487708 : ℝ) * ((2 * Θ * 0.000245163295 +
        (6863 / 10000) * 0.000245163295 * 13042 * 0.000980713286) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002836911281 + 0.000646361524 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13042 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13042 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13042 0.011 Θ ∧ gammaRatio 13042 0.011 Θ ≤ 0.000084280801 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13042 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035332487708 : ℝ) * 0.525 / ((1 - 0.011) * 13042) := by gcongr
      _ ≤ (0.000084280801 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13042 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13042 0.011 Θ) :=
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
    badAllowance 13042 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000383431726 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13042 BstLean.Part154.csC) 1.22 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 2 (rhoBar 13042 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13042 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13042 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13042 0.011 Θ) 1.12 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 1 (gammaRatio 13042 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13042 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13042 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13042 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13042 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035332487708 : ℝ) * 13042 *
        (1.3781E-8 / 1.1045361 + 1.6832E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000383431726 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13042 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003220343007 + 0.003204340550 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13042

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13042
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13042 BstLean.Part154.csC) (piBar (rhoBar 13042 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13042 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13042 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13042 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13042 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13042 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13042 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13042 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13042 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13042 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13042 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13042 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13042 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13042 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13042 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051784181679 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13042) ≤ 0.010457277571 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13042 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035332487708)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010457277571 + 2 * 0.737676 / 13042) := by gcongr
    _ ≤ (0.051784181679 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13042 12 ≤ 0.0015 := by
  exact BstLean.Part269.S27.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13042

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13042
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560518628975 : ℝ) ≤ plow 13042 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13042) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052409221796)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001342938989) : eMP 13042 0.011 xi bn ≤ 0.001156598504 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13042 : ℝ) * (1 - 0.011))) ≤ 0.000571916806 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001342938989 / (13042 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000571916806 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000571916806 : ℝ) + 3.141593 * 0.052409221796 / (13042 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001156598504 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052409221796)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001342938989) : PiBarMP 13042 12 0.011 xi bn ≤ 0.159101711143 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13042 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036646131979 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.571730637513 : ℝ) ≤ √((13042 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.201576171259 : ℝ) ≤ √(13042 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13042) ≤ 0.121998388550 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036646131979 + 0.052409221796 * 1.772454 / (2 * (113.571730637513 : ℝ))) * (1 + 0.001156598504) +
        8 / (13042 * 114.201576171259) + 0.121998388550 := by gcongr
    _ ≤ (0.159101711143 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052409221796)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001342938989) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280714786440) :
    parallelOracle 13042 0.011 xi bn cd ≤ 0.160066083295 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13042 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13042 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560518628975 : ℝ) ≤ plow 13042 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.201576171259 : ℝ) ≤ √(13042 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280714786440 : ℝ) / (2 * 0.560518628975 * 114.201576171259)) * 0.159101711143 +
        0.280714786440 ^ 2 / (2 * 0.560518628975 * 114.201576171259) := by gcongr
    _ ≤ (0.160066083295 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052409221796) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001342938989)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280714786440) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13042 13042 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560518628975 : ℝ) ≤ plow 13042 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.201576171259 : ℝ) ≤ √(13042 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13042 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13042 Θ 1.22 ≤ 0.011611928176 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.201576171259 := by gcongr <;> linarith
      _ ≤ (0.011611928176 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13042 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13042 13042 0.011 ≤ 0.008370172854 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13042 13042 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13042 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13042 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13042 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13042 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160066083295 + 0.011611928176 + (0.008370172854 : ℝ) *
        (1 + 2 * (0.280714786440 + 0.011611928176) / (0.560518628975 * 114.201576171259))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13042]

end BstLean.Part269.N13042

/-! The original eight local profiles supply actual 13042 moment certificates. -/
namespace BstLean.Part269.N13042
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13042 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13042 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13042 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052409221796 ∧
    0 ≤ bN 13042 BstLean.Part154.csC (groupTheta g) ∧ bN 13042 BstLean.Part154.csC (groupTheta g) ≤ 0.001342938989 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13042 13042 0.011
      (momentAllowance 13042 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13042 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13042 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13042 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13042 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13042 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228930604761 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13042 0.011
      (momentAllowance 13042 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13042 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13042
/-! The actual computed-centre upper energy formula at 13042. -/
namespace BstLean.Part269.N13042
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13042

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13042
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13042)
open BstLean.Part268 (cell13042)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084550836203
  | 2 => 0.085478082652
  | 3 => 0.086401323182
  | 4 => 0.087321471668
  | 5 => 0.088239648177
  | 6 => 0.089157211402
  | 7 => 0.090075794503
  | 8 => 0.090997344439
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13042 13042 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13042 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N13042

/-! Actual upper energy certificates on all 43 source endpoints at 13042. -/
namespace BstLean.Part269.N13042
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13042)
open BstLean.Part268 (cell13042)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13042 (gMinus 13042) (1 - (cell13042 i).lower) ≤ 1 ∧
    energyUpper 13042 (gMinus 13042) (BstLean.Part211.gPlus 13042)
      (finiteEnergy 13042 13042 0.011) (1 - (cell13042 i).lower) ≤
      (cell13042 i).energy := by
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
      have E := BstLean.Part269.S27.uniformEnergy10 (n := 13042) (by norm_num)
        (q := 1 - (cell13042 ⟨10,by decide⟩).lower)
        (by norm_num [cell13042]) (by norm_num [cell13042])
      exact ⟨E.1,E.2.trans (by norm_num [cell13042])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy11 (n := 13042) (by norm_num)
        (q := 1 - (cell13042 ⟨11,by decide⟩).lower)
        (by norm_num [cell13042]) (by norm_num [cell13042])
      exact ⟨E.1,E.2.trans (by norm_num [cell13042])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy12 (n := 13042) (by norm_num)
        (q := 1 - (cell13042 ⟨12,by decide⟩).lower)
        (by norm_num [cell13042]) (by norm_num [cell13042])
      exact ⟨E.1,E.2.trans (by norm_num [cell13042])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy13 (n := 13042) (by norm_num)
        (q := 1 - (cell13042 ⟨13,by decide⟩).lower)
        (by norm_num [cell13042]) (by norm_num [cell13042])
      exact ⟨E.1,E.2.trans (by norm_num [cell13042])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy14 (n := 13042) (by norm_num)
        (q := 1 - (cell13042 ⟨14,by decide⟩).lower)
        (by norm_num [cell13042]) (by norm_num [cell13042])
      exact ⟨E.1,E.2.trans (by norm_num [cell13042])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy15 (n := 13042) (by norm_num)
        (q := 1 - (cell13042 ⟨15,by decide⟩).lower)
        (by norm_num [cell13042]) (by norm_num [cell13042])
      exact ⟨E.1,E.2.trans (by norm_num [cell13042])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy16 (n := 13042) (by norm_num)
        (q := 1 - (cell13042 ⟨16,by decide⟩).lower)
        (by norm_num [cell13042]) (by norm_num [cell13042])
      exact ⟨E.1,E.2.trans (by norm_num [cell13042])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy17 (n := 13042) (by norm_num)
        (q := 1 - (cell13042 ⟨17,by decide⟩).lower)
        (by norm_num [cell13042]) (by norm_num [cell13042])
      exact ⟨E.1,E.2.trans (by norm_num [cell13042])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy18 (n := 13042) (by norm_num)
        (q := 1 - (cell13042 ⟨18,by decide⟩).lower)
        (by norm_num [cell13042]) (by norm_num [cell13042])
      exact ⟨E.1,E.2.trans (by norm_num [cell13042])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy19 (n := 13042) (by norm_num)
        (q := 1 - (cell13042 ⟨19,by decide⟩).lower)
        (by norm_num [cell13042]) (by norm_num [cell13042])
      exact ⟨E.1,E.2.trans (by norm_num [cell13042])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy20 (n := 13042) (by norm_num)
        (q := 1 - (cell13042 ⟨20,by decide⟩).lower)
        (by norm_num [cell13042]) (by norm_num [cell13042])
      exact ⟨E.1,E.2.trans (by norm_num [cell13042])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy21 (n := 13042) (by norm_num)
        (q := 1 - (cell13042 ⟨21,by decide⟩).lower)
        (by norm_num [cell13042]) (by norm_num [cell13042])
      exact ⟨E.1,E.2.trans (by norm_num [cell13042])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy22 (n := 13042) (by norm_num)
        (q := 1 - (cell13042 ⟨22,by decide⟩).lower)
        (by norm_num [cell13042]) (by norm_num [cell13042])
      exact ⟨E.1,E.2.trans (by norm_num [cell13042])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy23 (n := 13042) (by norm_num)
        (q := 1 - (cell13042 ⟨23,by decide⟩).lower)
        (by norm_num [cell13042]) (by norm_num [cell13042])
      exact ⟨E.1,E.2.trans (by norm_num [cell13042])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy24 (n := 13042) (by norm_num)
        (q := 1 - (cell13042 ⟨24,by decide⟩).lower)
        (by norm_num [cell13042]) (by norm_num [cell13042])
      exact ⟨E.1,E.2.trans (by norm_num [cell13042])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy25 (n := 13042) (by norm_num)
        (q := 1 - (cell13042 ⟨25,by decide⟩).lower)
        (by norm_num [cell13042]) (by norm_num [cell13042])
      exact ⟨E.1,E.2.trans (by norm_num [cell13042])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy26 (n := 13042) (by norm_num)
        (q := 1 - (cell13042 ⟨26,by decide⟩).lower)
        (by norm_num [cell13042]) (by norm_num [cell13042])
      exact ⟨E.1,E.2.trans (by norm_num [cell13042])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy27 (n := 13042) (by norm_num)
        (q := 1 - (cell13042 ⟨27,by decide⟩).lower)
        (by norm_num [cell13042]) (by norm_num [cell13042])
      exact ⟨E.1,E.2.trans (by norm_num [cell13042])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy28 (n := 13042) (by norm_num)
        (q := 1 - (cell13042 ⟨28,by decide⟩).lower)
        (by norm_num [cell13042]) (by norm_num [cell13042])
      exact ⟨E.1,E.2.trans (by norm_num [cell13042])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy29 (n := 13042) (by norm_num)
        (q := 1 - (cell13042 ⟨29,by decide⟩).lower)
        (by norm_num [cell13042]) (by norm_num [cell13042])
      exact ⟨E.1,E.2.trans (by norm_num [cell13042])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy30 (n := 13042) (by norm_num)
        (q := 1 - (cell13042 ⟨30,by decide⟩).lower)
        (by norm_num [cell13042]) (by norm_num [cell13042])
      exact ⟨E.1,E.2.trans (by norm_num [cell13042])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy31 (n := 13042) (by norm_num)
        (q := 1 - (cell13042 ⟨31,by decide⟩).lower)
        (by norm_num [cell13042]) (by norm_num [cell13042])
      exact ⟨E.1,E.2.trans (by norm_num [cell13042])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy32 (n := 13042) (by norm_num)
        (q := 1 - (cell13042 ⟨32,by decide⟩).lower)
        (by norm_num [cell13042]) (by norm_num [cell13042])
      exact ⟨E.1,E.2.trans (by norm_num [cell13042])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy33 (n := 13042) (by norm_num)
        (q := 1 - (cell13042 ⟨33,by decide⟩).lower)
        (by norm_num [cell13042]) (by norm_num [cell13042])
      exact ⟨E.1,E.2.trans (by norm_num [cell13042])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy34 (n := 13042) (by norm_num)
        (q := 1 - (cell13042 ⟨34,by decide⟩).lower)
        (by norm_num [cell13042]) (by norm_num [cell13042])
      exact ⟨E.1,E.2.trans (by norm_num [cell13042])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy35 (n := 13042) (by norm_num)
        (q := 1 - (cell13042 ⟨35,by decide⟩).lower)
        (by norm_num [cell13042]) (by norm_num [cell13042])
      exact ⟨E.1,E.2.trans (by norm_num [cell13042])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy36 (n := 13042) (by norm_num)
        (q := 1 - (cell13042 ⟨36,by decide⟩).lower)
        (by norm_num [cell13042]) (by norm_num [cell13042])
      exact ⟨E.1,E.2.trans (by norm_num [cell13042])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy37 (n := 13042) (by norm_num)
        (q := 1 - (cell13042 ⟨37,by decide⟩).lower)
        (by norm_num [cell13042]) (by norm_num [cell13042])
      exact ⟨E.1,E.2.trans (by norm_num [cell13042])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy38 (n := 13042) (by norm_num)
        (q := 1 - (cell13042 ⟨38,by decide⟩).lower)
        (by norm_num [cell13042]) (by norm_num [cell13042])
      exact ⟨E.1,E.2.trans (by norm_num [cell13042])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy39 (n := 13042) (by norm_num)
        (q := 1 - (cell13042 ⟨39,by decide⟩).lower)
        (by norm_num [cell13042]) (by norm_num [cell13042])
      exact ⟨E.1,E.2.trans (by norm_num [cell13042])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy40 (n := 13042) (by norm_num)
        (q := 1 - (cell13042 ⟨40,by decide⟩).lower)
        (by norm_num [cell13042]) (by norm_num [cell13042])
      exact ⟨E.1,E.2.trans (by norm_num [cell13042])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy41 (n := 13042) (by norm_num)
        (q := 1 - (cell13042 ⟨41,by decide⟩).lower)
        (by norm_num [cell13042]) (by norm_num [cell13042])
      exact ⟨E.1,E.2.trans (by norm_num [cell13042])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy42 (n := 13042) (by norm_num)
        (q := 1 - (cell13042 ⟨42,by decide⟩).lower)
        (by norm_num [cell13042]) (by norm_num [cell13042])
      exact ⟨E.1,E.2.trans (by norm_num [cell13042])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy43 (n := 13042) (by norm_num)
        (q := 1 - (cell13042 ⟨43,by decide⟩).lower)
        (by norm_num [cell13042]) (by norm_num [cell13042])
      exact ⟨E.1,E.2.trans (by norm_num [cell13042])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy44 (n := 13042) (by norm_num)
        (q := 1 - (cell13042 ⟨44,by decide⟩).lower)
        (by norm_num [cell13042]) (by norm_num [cell13042])
      exact ⟨E.1,E.2.trans (by norm_num [cell13042])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy45 (n := 13042) (by norm_num)
        (q := 1 - (cell13042 ⟨45,by decide⟩).lower)
        (by norm_num [cell13042]) (by norm_num [cell13042])
      exact ⟨E.1,E.2.trans (by norm_num [cell13042])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy46 (n := 13042) (by norm_num)
        (q := 1 - (cell13042 ⟨46,by decide⟩).lower)
        (by norm_num [cell13042]) (by norm_num [cell13042])
      exact ⟨E.1,E.2.trans (by norm_num [cell13042])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy47 (n := 13042) (by norm_num)
        (q := 1 - (cell13042 ⟨47,by decide⟩).lower)
        (by norm_num [cell13042]) (by norm_num [cell13042])
      exact ⟨E.1,E.2.trans (by norm_num [cell13042])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy48 (n := 13042) (by norm_num)
        (q := 1 - (cell13042 ⟨48,by decide⟩).lower)
        (by norm_num [cell13042]) (by norm_num [cell13042])
      exact ⟨E.1,E.2.trans (by norm_num [cell13042])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy49 (n := 13042) (by norm_num)
        (q := 1 - (cell13042 ⟨49,by decide⟩).lower)
        (by norm_num [cell13042]) (by norm_num [cell13042])
      exact ⟨E.1,E.2.trans (by norm_num [cell13042])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy50 (n := 13042) (by norm_num)
        (q := 1 - (cell13042 ⟨50,by decide⟩).lower)
        (by norm_num [cell13042]) (by norm_num [cell13042])
      exact ⟨E.1,E.2.trans (by norm_num [cell13042])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy51 (n := 13042) (by norm_num)
        (q := 1 - (cell13042 ⟨51,by decide⟩).lower)
        (by norm_num [cell13042]) (by norm_num [cell13042])
      exact ⟨E.1,E.2.trans (by norm_num [cell13042])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy52 (n := 13042) (by norm_num)
        (q := 1 - (cell13042 ⟨52,by decide⟩).lower)
        (by norm_num [cell13042]) (by norm_num [cell13042])
      exact ⟨E.1,E.2.trans (by norm_num [cell13042])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13042

/-! Source-cell containment and simple scalar guards at 13042. -/
namespace BstLean.Part269.N13042
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13042)
open BstLean.Part268 (cell13042)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13042 ⟨10,by decide⟩).lower ∧ (cell13042 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13042 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13042 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13042 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13042 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13042 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13042,cell13042,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13042 ⟨11,by decide⟩).lower ∧ (cell13042 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13042 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13042 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13042 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13042 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13042 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13042,cell13042,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13042 ⟨12,by decide⟩).lower ∧ (cell13042 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13042 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13042 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13042 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13042 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13042 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13042,cell13042,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13042 ⟨13,by decide⟩).lower ∧ (cell13042 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13042 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13042 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13042 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13042 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13042 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13042,cell13042,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13042 ⟨14,by decide⟩).lower ∧ (cell13042 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13042 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13042 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13042 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13042 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13042 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13042,cell13042,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13042 ⟨15,by decide⟩).lower ∧ (cell13042 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13042 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13042 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13042 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13042 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13042 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13042,cell13042,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13042 ⟨16,by decide⟩).lower ∧ (cell13042 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13042 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13042 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13042 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13042 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13042 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13042,cell13042,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13042 ⟨17,by decide⟩).lower ∧ (cell13042 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13042 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13042 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13042 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13042 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13042 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13042,cell13042,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13042 ⟨18,by decide⟩).lower ∧ (cell13042 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13042 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13042 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13042 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13042 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13042 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13042,cell13042,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13042 ⟨19,by decide⟩).lower ∧ (cell13042 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13042 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13042 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13042 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13042 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13042 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13042,cell13042,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13042 ⟨20,by decide⟩).lower ∧ (cell13042 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13042 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13042 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13042 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13042 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13042 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13042,cell13042,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13042 ⟨21,by decide⟩).lower ∧ (cell13042 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13042 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13042 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13042 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13042 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13042 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13042,cell13042,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13042 ⟨22,by decide⟩).lower ∧ (cell13042 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13042 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13042 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13042 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13042 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13042 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13042,cell13042,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13042 ⟨23,by decide⟩).lower ∧ (cell13042 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13042 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13042 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13042 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13042 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13042 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13042,cell13042,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13042 ⟨24,by decide⟩).lower ∧ (cell13042 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13042 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13042 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13042 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13042 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13042 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13042,cell13042,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13042 ⟨25,by decide⟩).lower ∧ (cell13042 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13042 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13042 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13042 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13042 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13042 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13042,cell13042,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13042 ⟨26,by decide⟩).lower ∧ (cell13042 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13042 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13042 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13042 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13042 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13042 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13042,cell13042,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13042 ⟨27,by decide⟩).lower ∧ (cell13042 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13042 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13042 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13042 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13042 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13042 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13042,cell13042,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13042 ⟨28,by decide⟩).lower ∧ (cell13042 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13042 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13042 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13042 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13042 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13042 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13042,cell13042,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13042 ⟨29,by decide⟩).lower ∧ (cell13042 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13042 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13042 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13042 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13042 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13042 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13042,cell13042,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13042 ⟨30,by decide⟩).lower ∧ (cell13042 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13042 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13042 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13042 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13042 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13042 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13042,cell13042,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13042 ⟨31,by decide⟩).lower ∧ (cell13042 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13042 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13042 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13042 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13042 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13042 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13042,cell13042,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13042 ⟨32,by decide⟩).lower ∧ (cell13042 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13042 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13042 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13042 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13042 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13042 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13042,cell13042,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13042 ⟨33,by decide⟩).lower ∧ (cell13042 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13042 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13042 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13042 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13042 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13042 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13042,cell13042,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13042 ⟨34,by decide⟩).lower ∧ (cell13042 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13042 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13042 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13042 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13042 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13042 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13042,cell13042,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13042 ⟨35,by decide⟩).lower ∧ (cell13042 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13042 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13042 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13042 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13042 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13042 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13042,cell13042,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13042 ⟨36,by decide⟩).lower ∧ (cell13042 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13042 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13042 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13042 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13042 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13042 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13042,cell13042,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13042 ⟨37,by decide⟩).lower ∧ (cell13042 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13042 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13042 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13042 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13042 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13042 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13042,cell13042,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13042 ⟨38,by decide⟩).lower ∧ (cell13042 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13042 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13042 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13042 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13042 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13042 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13042,cell13042,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13042 ⟨39,by decide⟩).lower ∧ (cell13042 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13042 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13042 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13042 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13042 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13042 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13042,cell13042,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13042 ⟨40,by decide⟩).lower ∧ (cell13042 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13042 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13042 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13042 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13042 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13042 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13042,cell13042,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13042 ⟨41,by decide⟩).lower ∧ (cell13042 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13042 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13042 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13042 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13042 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13042 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13042,cell13042,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13042 ⟨42,by decide⟩).lower ∧ (cell13042 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13042 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13042 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13042 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13042 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13042 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13042,cell13042,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13042 ⟨43,by decide⟩).lower ∧ (cell13042 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13042 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13042 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13042 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13042 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13042 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13042,cell13042,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13042 ⟨44,by decide⟩).lower ∧ (cell13042 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13042 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13042 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13042 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13042 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13042 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13042,cell13042,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13042 ⟨45,by decide⟩).lower ∧ (cell13042 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13042 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13042 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13042 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13042 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13042 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13042,cell13042,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13042 ⟨46,by decide⟩).lower ∧ (cell13042 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13042 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13042 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13042 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13042 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13042 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13042,cell13042,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13042 ⟨47,by decide⟩).lower ∧ (cell13042 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13042 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13042 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13042 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13042 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13042 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13042,cell13042,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13042 ⟨48,by decide⟩).lower ∧ (cell13042 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13042 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13042 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13042 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13042 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13042 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13042,cell13042,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13042 ⟨49,by decide⟩).lower ∧ (cell13042 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13042 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13042 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13042 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13042 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13042 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13042,cell13042,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13042 ⟨50,by decide⟩).lower ∧ (cell13042 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13042 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13042 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13042 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13042 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13042 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13042,cell13042,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13042 ⟨51,by decide⟩).lower ∧ (cell13042 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13042 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13042 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13042 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13042 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13042 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13042,cell13042,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13042 ⟨52,by decide⟩).lower ∧ (cell13042 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13042 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13042 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13042 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13042 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13042 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13042,cell13042,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13042 i).lower ∧
    (cell13042 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13042 i).upper ≤ (0.532 : ℝ) ∧
    (cell13042 i).centre ≤ (0.1 : ℝ) ∧ (cell13042 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13042 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13042 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13042

/-! The local source numeric instances at 13042 have no network premises. -/
namespace BstLean.Part269.N13042
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13042)
open BstLean.Part268 (cell13042)

noncomputable def sourceNumerics13042 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13042 (cell13042 i)
      scalarRow13042.M scalarRow13042.H scalarRow13042.xi := by
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
    energy_allowance := scalarRow13042.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13042]
    centre_nonneg := (scalarRow13042.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D27.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13042])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13042
/-! Actual 13043 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13043
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13043 ≤ (1.035331121464 : ℝ) := by
  have hr : (114.205954310622 : ℝ) ≤ √(13043 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.205954310622 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13043 13043 (11 / 1000) ≤
    (0.008369851977 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13043) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.205954310622 : ℝ) ≤ √(13043 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13043)
  have hdiv : K / √(13043 : ℝ) ≤ K / 114.205954310622 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.205954310622 ≤ (0.008369851977 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13043.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13043 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13043 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13043 := gPlus_lower 13043
end BstLean.Part269.N13043

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13043
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035331121463 : ℝ) ≤ wn 13043 := by
  have hn : √(13043 : ℝ) ≤ 114.205954310623 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13043 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.205954310623 ≤ 2 / √(13043 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000245143795 : ℝ) ≤ rhoBar 13043 BstLean.Part154.csC ∧
    rhoBar 13043 BstLean.Part154.csC ≤ 0.000245144175 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035331121463 : ℝ) / (1.295212 * 13043) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035331121464 : ℝ) / (1.29521 * 13043) := by gcongr
      _ ≤ (0.000245144175 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13043 BstLean.Part154.csC) ≤ 0.000980636796 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13043 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13043 BstLean.Part154.csC) (piBar (rhoBar 13043 BstLean.Part154.csC)) ≤ 0.000187242542 ∧
    cc1 (rhoBar 13043 BstLean.Part154.csC) (piBar (rhoBar 13043 BstLean.Part154.csC)) ≤ 0.000119143720 ∧
    cc2 (rhoBar 13043 BstLean.Part154.csC) ≤ 0.000069163901 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13043 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13043 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13043 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13043 BstLean.Part154.csC * nuR (rhoBar 13043 BstLean.Part154.csC)) ≤ 0.000490303374 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000245144175 : ℝ) * 0.000980636796 := by gcongr
      _ ≤ (0.000490303374 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13043 BstLean.Part154.csC) * nuR (rhoBar 13043 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000980636796 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13043 BstLean.Part154.csC) * rhoBar 13043 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000245144175 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000245144175 / 2 + 0.399 * 0.000980636796 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000187242542 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000490303374 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119143720 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000245144175 / 1.414213562 := by gcongr
      _ ≤ (0.000069163901 : ℝ) := by norm_num

end BstLean.Part269.N13043

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13043
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13043 BstLean.Part154.csC) (piBar (rhoBar 13043 BstLean.Part154.csC)) ≤ 1.51407E-7 := by
  have hr0 : 0 ≤ rhoBar 13043 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13043 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13043 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13043 BstLean.Part154.csC) (piBar (rhoBar 13043 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13043 BstLean.Part154.csC) (piBar (rhoBar 13043 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13043 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000187242542 : ℝ) ^ 2 + 0.000119143720 ^ 2 + 3 * 0.000069163901 ^ 2 +
        2 * 0.797885 * 0.000187242542 * 0.000119143720 + 2 * 0.000187242542 * 0.000069163901 +
        4 * 0.797885 * 0.000119143720 * 0.000069163901 := by gcongr
    _ ≤ (1.51407E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13043 BstLean.Part154.csC Θ ≤ 0.002557786611 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13043 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13043 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13043 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13043 BstLean.Part154.csC) (piBar (rhoBar 13043 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13043 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035331121464 * 1.51407E-7 / (0.000245143795 : ℝ) := by gcongr
    _ ≤ 0.002557786611 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13043 BstLean.Part154.csC Θ ≤ 0.002836682532 + 0.000646310263 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13043 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13043 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13043 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035331121464 : ℝ) * ((2 * Θ * 0.000245144175 +
        (6863 / 10000) * 0.000245144175 * 13043 * 0.000980636796) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002836682532 + 0.000646310263 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13043 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13043 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13043 0.011 Θ ∧ gammaRatio 13043 0.011 Θ ≤ 0.000084274228 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13043 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035331121464 : ℝ) * 0.525 / ((1 - 0.011) * 13043) := by gcongr
      _ ≤ (0.000084274228 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13043 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13043 0.011 Θ) :=
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
    badAllowance 13043 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000383431726 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13043 BstLean.Part154.csC) 1.22 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 2 (rhoBar 13043 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13043 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13043 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13043 0.011 Θ) 1.12 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 1 (gammaRatio 13043 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13043 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13043 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13043 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13043 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035331121464 : ℝ) * 13043 *
        (1.3781E-8 / 1.1045361 + 1.6832E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000383431726 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13043 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003220114258 + 0.003204096874 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13043

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13043
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13043 BstLean.Part154.csC) (piBar (rhoBar 13043 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13043 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13043 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13043 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13043 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13043 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13043 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13043 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13043 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13043 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13043 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13043 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13043 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13043 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13043 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051782175267 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13043) ≤ 0.010456876687 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13043 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035331121464)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010456876687 + 2 * 0.737676 / 13043) := by gcongr
    _ ≤ (0.051782175267 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13043 12 ≤ 0.0015 := by
  exact BstLean.Part269.S27.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13043

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13043
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560518671854 : ℝ) ≤ plow 13043 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13043) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052408865117)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001342837971) : eMP 13043 0.011 xi bn ≤ 0.001156510569 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13043 : ℝ) * (1 - 0.011))) ≤ 0.000571873371 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001342837971 / (13043 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000571873371 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000571873371 : ℝ) + 3.141593 * 0.052408865117 / (13043 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001156510569 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052408865117)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001342837971) : PiBarMP 13043 12 0.011 xi bn ≤ 0.159095632008 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13043 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036644753663 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.576084630524 : ℝ) ≤ √((13043 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.205954310622 : ℝ) ≤ √(13043 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13043) ≤ 0.121993711684 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036644753663 + 0.052408865117 * 1.772454 / (2 * (113.576084630524 : ℝ))) * (1 + 0.001156510569) +
        8 / (13043 * 114.205954310622) + 0.121993711684 := by gcongr
    _ ≤ (0.159095632008 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052408865117)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001342837971) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280712001015) :
    parallelOracle 13043 0.011 xi bn cd ≤ 0.160059938111 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13043 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13043 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560518671854 : ℝ) ≤ plow 13043 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.205954310622 : ℝ) ≤ √(13043 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280712001015 : ℝ) / (2 * 0.560518671854 * 114.205954310622)) * 0.159095632008 +
        0.280712001015 ^ 2 / (2 * 0.560518671854 * 114.205954310622) := by gcongr
    _ ≤ (0.160059938111 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052408865117) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001342837971)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280712001015) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13043 13043 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560518671854 : ℝ) ≤ plow 13043 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.205954310622 : ℝ) ≤ √(13043 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13043 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13043 Θ 1.22 ≤ 0.011611483027 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.205954310622 := by gcongr <;> linarith
      _ ≤ (0.011611483027 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13043 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13043 13043 0.011 ≤ 0.008369851977 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13043 13043 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13043 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13043 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13043 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13043 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160059938111 + 0.011611483027 + (0.008369851977 : ℝ) *
        (1 + 2 * (0.280712001015 + 0.011611483027) / (0.560518671854 * 114.205954310622))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13043]

end BstLean.Part269.N13043

/-! The original eight local profiles supply actual 13043 moment certificates. -/
namespace BstLean.Part269.N13043
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13043 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13043 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13043 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052408865117 ∧
    0 ≤ bN 13043 BstLean.Part154.csC (groupTheta g) ∧ bN 13043 BstLean.Part154.csC (groupTheta g) ≤ 0.001342837971 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13043 13043 0.011
      (momentAllowance 13043 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13043 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13043 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13043 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13043 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13043 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228929825748 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13043 0.011
      (momentAllowance 13043 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13043 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13043
/-! The actual computed-centre upper energy formula at 13043. -/
namespace BstLean.Part269.N13043
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13043

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13043
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13043)
open BstLean.Part268 (cell13043)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084548251248
  | 2 => 0.085475464315
  | 3 => 0.086398666488
  | 4 => 0.087318770470
  | 5 => 0.088236894940
  | 6 => 0.089154396961
  | 7 => 0.090072907788
  | 8 => 0.090994372169
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13043 13043 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13043 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N13043

/-! Actual upper energy certificates on all 43 source endpoints at 13043. -/
namespace BstLean.Part269.N13043
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13043)
open BstLean.Part268 (cell13043)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13043 (gMinus 13043) (1 - (cell13043 i).lower) ≤ 1 ∧
    energyUpper 13043 (gMinus 13043) (BstLean.Part211.gPlus 13043)
      (finiteEnergy 13043 13043 0.011) (1 - (cell13043 i).lower) ≤
      (cell13043 i).energy := by
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
      have E := BstLean.Part269.S27.uniformEnergy10 (n := 13043) (by norm_num)
        (q := 1 - (cell13043 ⟨10,by decide⟩).lower)
        (by norm_num [cell13043]) (by norm_num [cell13043])
      exact ⟨E.1,E.2.trans (by norm_num [cell13043])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy11 (n := 13043) (by norm_num)
        (q := 1 - (cell13043 ⟨11,by decide⟩).lower)
        (by norm_num [cell13043]) (by norm_num [cell13043])
      exact ⟨E.1,E.2.trans (by norm_num [cell13043])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy12 (n := 13043) (by norm_num)
        (q := 1 - (cell13043 ⟨12,by decide⟩).lower)
        (by norm_num [cell13043]) (by norm_num [cell13043])
      exact ⟨E.1,E.2.trans (by norm_num [cell13043])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy13 (n := 13043) (by norm_num)
        (q := 1 - (cell13043 ⟨13,by decide⟩).lower)
        (by norm_num [cell13043]) (by norm_num [cell13043])
      exact ⟨E.1,E.2.trans (by norm_num [cell13043])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy14 (n := 13043) (by norm_num)
        (q := 1 - (cell13043 ⟨14,by decide⟩).lower)
        (by norm_num [cell13043]) (by norm_num [cell13043])
      exact ⟨E.1,E.2.trans (by norm_num [cell13043])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy15 (n := 13043) (by norm_num)
        (q := 1 - (cell13043 ⟨15,by decide⟩).lower)
        (by norm_num [cell13043]) (by norm_num [cell13043])
      exact ⟨E.1,E.2.trans (by norm_num [cell13043])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy16 (n := 13043) (by norm_num)
        (q := 1 - (cell13043 ⟨16,by decide⟩).lower)
        (by norm_num [cell13043]) (by norm_num [cell13043])
      exact ⟨E.1,E.2.trans (by norm_num [cell13043])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy17 (n := 13043) (by norm_num)
        (q := 1 - (cell13043 ⟨17,by decide⟩).lower)
        (by norm_num [cell13043]) (by norm_num [cell13043])
      exact ⟨E.1,E.2.trans (by norm_num [cell13043])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy18 (n := 13043) (by norm_num)
        (q := 1 - (cell13043 ⟨18,by decide⟩).lower)
        (by norm_num [cell13043]) (by norm_num [cell13043])
      exact ⟨E.1,E.2.trans (by norm_num [cell13043])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy19 (n := 13043) (by norm_num)
        (q := 1 - (cell13043 ⟨19,by decide⟩).lower)
        (by norm_num [cell13043]) (by norm_num [cell13043])
      exact ⟨E.1,E.2.trans (by norm_num [cell13043])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy20 (n := 13043) (by norm_num)
        (q := 1 - (cell13043 ⟨20,by decide⟩).lower)
        (by norm_num [cell13043]) (by norm_num [cell13043])
      exact ⟨E.1,E.2.trans (by norm_num [cell13043])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy21 (n := 13043) (by norm_num)
        (q := 1 - (cell13043 ⟨21,by decide⟩).lower)
        (by norm_num [cell13043]) (by norm_num [cell13043])
      exact ⟨E.1,E.2.trans (by norm_num [cell13043])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy22 (n := 13043) (by norm_num)
        (q := 1 - (cell13043 ⟨22,by decide⟩).lower)
        (by norm_num [cell13043]) (by norm_num [cell13043])
      exact ⟨E.1,E.2.trans (by norm_num [cell13043])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy23 (n := 13043) (by norm_num)
        (q := 1 - (cell13043 ⟨23,by decide⟩).lower)
        (by norm_num [cell13043]) (by norm_num [cell13043])
      exact ⟨E.1,E.2.trans (by norm_num [cell13043])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy24 (n := 13043) (by norm_num)
        (q := 1 - (cell13043 ⟨24,by decide⟩).lower)
        (by norm_num [cell13043]) (by norm_num [cell13043])
      exact ⟨E.1,E.2.trans (by norm_num [cell13043])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy25 (n := 13043) (by norm_num)
        (q := 1 - (cell13043 ⟨25,by decide⟩).lower)
        (by norm_num [cell13043]) (by norm_num [cell13043])
      exact ⟨E.1,E.2.trans (by norm_num [cell13043])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy26 (n := 13043) (by norm_num)
        (q := 1 - (cell13043 ⟨26,by decide⟩).lower)
        (by norm_num [cell13043]) (by norm_num [cell13043])
      exact ⟨E.1,E.2.trans (by norm_num [cell13043])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy27 (n := 13043) (by norm_num)
        (q := 1 - (cell13043 ⟨27,by decide⟩).lower)
        (by norm_num [cell13043]) (by norm_num [cell13043])
      exact ⟨E.1,E.2.trans (by norm_num [cell13043])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy28 (n := 13043) (by norm_num)
        (q := 1 - (cell13043 ⟨28,by decide⟩).lower)
        (by norm_num [cell13043]) (by norm_num [cell13043])
      exact ⟨E.1,E.2.trans (by norm_num [cell13043])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy29 (n := 13043) (by norm_num)
        (q := 1 - (cell13043 ⟨29,by decide⟩).lower)
        (by norm_num [cell13043]) (by norm_num [cell13043])
      exact ⟨E.1,E.2.trans (by norm_num [cell13043])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy30 (n := 13043) (by norm_num)
        (q := 1 - (cell13043 ⟨30,by decide⟩).lower)
        (by norm_num [cell13043]) (by norm_num [cell13043])
      exact ⟨E.1,E.2.trans (by norm_num [cell13043])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy31 (n := 13043) (by norm_num)
        (q := 1 - (cell13043 ⟨31,by decide⟩).lower)
        (by norm_num [cell13043]) (by norm_num [cell13043])
      exact ⟨E.1,E.2.trans (by norm_num [cell13043])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy32 (n := 13043) (by norm_num)
        (q := 1 - (cell13043 ⟨32,by decide⟩).lower)
        (by norm_num [cell13043]) (by norm_num [cell13043])
      exact ⟨E.1,E.2.trans (by norm_num [cell13043])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy33 (n := 13043) (by norm_num)
        (q := 1 - (cell13043 ⟨33,by decide⟩).lower)
        (by norm_num [cell13043]) (by norm_num [cell13043])
      exact ⟨E.1,E.2.trans (by norm_num [cell13043])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy34 (n := 13043) (by norm_num)
        (q := 1 - (cell13043 ⟨34,by decide⟩).lower)
        (by norm_num [cell13043]) (by norm_num [cell13043])
      exact ⟨E.1,E.2.trans (by norm_num [cell13043])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy35 (n := 13043) (by norm_num)
        (q := 1 - (cell13043 ⟨35,by decide⟩).lower)
        (by norm_num [cell13043]) (by norm_num [cell13043])
      exact ⟨E.1,E.2.trans (by norm_num [cell13043])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy36 (n := 13043) (by norm_num)
        (q := 1 - (cell13043 ⟨36,by decide⟩).lower)
        (by norm_num [cell13043]) (by norm_num [cell13043])
      exact ⟨E.1,E.2.trans (by norm_num [cell13043])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy37 (n := 13043) (by norm_num)
        (q := 1 - (cell13043 ⟨37,by decide⟩).lower)
        (by norm_num [cell13043]) (by norm_num [cell13043])
      exact ⟨E.1,E.2.trans (by norm_num [cell13043])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy38 (n := 13043) (by norm_num)
        (q := 1 - (cell13043 ⟨38,by decide⟩).lower)
        (by norm_num [cell13043]) (by norm_num [cell13043])
      exact ⟨E.1,E.2.trans (by norm_num [cell13043])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy39 (n := 13043) (by norm_num)
        (q := 1 - (cell13043 ⟨39,by decide⟩).lower)
        (by norm_num [cell13043]) (by norm_num [cell13043])
      exact ⟨E.1,E.2.trans (by norm_num [cell13043])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy40 (n := 13043) (by norm_num)
        (q := 1 - (cell13043 ⟨40,by decide⟩).lower)
        (by norm_num [cell13043]) (by norm_num [cell13043])
      exact ⟨E.1,E.2.trans (by norm_num [cell13043])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy41 (n := 13043) (by norm_num)
        (q := 1 - (cell13043 ⟨41,by decide⟩).lower)
        (by norm_num [cell13043]) (by norm_num [cell13043])
      exact ⟨E.1,E.2.trans (by norm_num [cell13043])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy42 (n := 13043) (by norm_num)
        (q := 1 - (cell13043 ⟨42,by decide⟩).lower)
        (by norm_num [cell13043]) (by norm_num [cell13043])
      exact ⟨E.1,E.2.trans (by norm_num [cell13043])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy43 (n := 13043) (by norm_num)
        (q := 1 - (cell13043 ⟨43,by decide⟩).lower)
        (by norm_num [cell13043]) (by norm_num [cell13043])
      exact ⟨E.1,E.2.trans (by norm_num [cell13043])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy44 (n := 13043) (by norm_num)
        (q := 1 - (cell13043 ⟨44,by decide⟩).lower)
        (by norm_num [cell13043]) (by norm_num [cell13043])
      exact ⟨E.1,E.2.trans (by norm_num [cell13043])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy45 (n := 13043) (by norm_num)
        (q := 1 - (cell13043 ⟨45,by decide⟩).lower)
        (by norm_num [cell13043]) (by norm_num [cell13043])
      exact ⟨E.1,E.2.trans (by norm_num [cell13043])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy46 (n := 13043) (by norm_num)
        (q := 1 - (cell13043 ⟨46,by decide⟩).lower)
        (by norm_num [cell13043]) (by norm_num [cell13043])
      exact ⟨E.1,E.2.trans (by norm_num [cell13043])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy47 (n := 13043) (by norm_num)
        (q := 1 - (cell13043 ⟨47,by decide⟩).lower)
        (by norm_num [cell13043]) (by norm_num [cell13043])
      exact ⟨E.1,E.2.trans (by norm_num [cell13043])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy48 (n := 13043) (by norm_num)
        (q := 1 - (cell13043 ⟨48,by decide⟩).lower)
        (by norm_num [cell13043]) (by norm_num [cell13043])
      exact ⟨E.1,E.2.trans (by norm_num [cell13043])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy49 (n := 13043) (by norm_num)
        (q := 1 - (cell13043 ⟨49,by decide⟩).lower)
        (by norm_num [cell13043]) (by norm_num [cell13043])
      exact ⟨E.1,E.2.trans (by norm_num [cell13043])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy50 (n := 13043) (by norm_num)
        (q := 1 - (cell13043 ⟨50,by decide⟩).lower)
        (by norm_num [cell13043]) (by norm_num [cell13043])
      exact ⟨E.1,E.2.trans (by norm_num [cell13043])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy51 (n := 13043) (by norm_num)
        (q := 1 - (cell13043 ⟨51,by decide⟩).lower)
        (by norm_num [cell13043]) (by norm_num [cell13043])
      exact ⟨E.1,E.2.trans (by norm_num [cell13043])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy52 (n := 13043) (by norm_num)
        (q := 1 - (cell13043 ⟨52,by decide⟩).lower)
        (by norm_num [cell13043]) (by norm_num [cell13043])
      exact ⟨E.1,E.2.trans (by norm_num [cell13043])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13043

/-! Source-cell containment and simple scalar guards at 13043. -/
namespace BstLean.Part269.N13043
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13043)
open BstLean.Part268 (cell13043)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13043 ⟨10,by decide⟩).lower ∧ (cell13043 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13043 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13043 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13043 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13043 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13043 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13043,cell13043,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13043 ⟨11,by decide⟩).lower ∧ (cell13043 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13043 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13043 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13043 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13043 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13043 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13043,cell13043,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13043 ⟨12,by decide⟩).lower ∧ (cell13043 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13043 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13043 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13043 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13043 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13043 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13043,cell13043,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13043 ⟨13,by decide⟩).lower ∧ (cell13043 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13043 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13043 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13043 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13043 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13043 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13043,cell13043,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13043 ⟨14,by decide⟩).lower ∧ (cell13043 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13043 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13043 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13043 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13043 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13043 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13043,cell13043,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13043 ⟨15,by decide⟩).lower ∧ (cell13043 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13043 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13043 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13043 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13043 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13043 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13043,cell13043,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13043 ⟨16,by decide⟩).lower ∧ (cell13043 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13043 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13043 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13043 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13043 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13043 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13043,cell13043,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13043 ⟨17,by decide⟩).lower ∧ (cell13043 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13043 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13043 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13043 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13043 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13043 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13043,cell13043,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13043 ⟨18,by decide⟩).lower ∧ (cell13043 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13043 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13043 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13043 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13043 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13043 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13043,cell13043,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13043 ⟨19,by decide⟩).lower ∧ (cell13043 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13043 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13043 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13043 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13043 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13043 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13043,cell13043,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13043 ⟨20,by decide⟩).lower ∧ (cell13043 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13043 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13043 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13043 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13043 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13043 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13043,cell13043,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13043 ⟨21,by decide⟩).lower ∧ (cell13043 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13043 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13043 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13043 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13043 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13043 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13043,cell13043,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13043 ⟨22,by decide⟩).lower ∧ (cell13043 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13043 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13043 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13043 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13043 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13043 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13043,cell13043,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13043 ⟨23,by decide⟩).lower ∧ (cell13043 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13043 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13043 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13043 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13043 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13043 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13043,cell13043,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13043 ⟨24,by decide⟩).lower ∧ (cell13043 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13043 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13043 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13043 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13043 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13043 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13043,cell13043,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13043 ⟨25,by decide⟩).lower ∧ (cell13043 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13043 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13043 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13043 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13043 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13043 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13043,cell13043,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13043 ⟨26,by decide⟩).lower ∧ (cell13043 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13043 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13043 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13043 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13043 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13043 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13043,cell13043,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13043 ⟨27,by decide⟩).lower ∧ (cell13043 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13043 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13043 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13043 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13043 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13043 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13043,cell13043,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13043 ⟨28,by decide⟩).lower ∧ (cell13043 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13043 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13043 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13043 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13043 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13043 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13043,cell13043,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13043 ⟨29,by decide⟩).lower ∧ (cell13043 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13043 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13043 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13043 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13043 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13043 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13043,cell13043,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13043 ⟨30,by decide⟩).lower ∧ (cell13043 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13043 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13043 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13043 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13043 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13043 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13043,cell13043,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13043 ⟨31,by decide⟩).lower ∧ (cell13043 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13043 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13043 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13043 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13043 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13043 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13043,cell13043,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13043 ⟨32,by decide⟩).lower ∧ (cell13043 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13043 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13043 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13043 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13043 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13043 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13043,cell13043,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13043 ⟨33,by decide⟩).lower ∧ (cell13043 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13043 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13043 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13043 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13043 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13043 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13043,cell13043,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13043 ⟨34,by decide⟩).lower ∧ (cell13043 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13043 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13043 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13043 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13043 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13043 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13043,cell13043,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13043 ⟨35,by decide⟩).lower ∧ (cell13043 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13043 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13043 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13043 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13043 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13043 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13043,cell13043,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13043 ⟨36,by decide⟩).lower ∧ (cell13043 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13043 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13043 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13043 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13043 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13043 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13043,cell13043,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13043 ⟨37,by decide⟩).lower ∧ (cell13043 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13043 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13043 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13043 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13043 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13043 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13043,cell13043,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13043 ⟨38,by decide⟩).lower ∧ (cell13043 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13043 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13043 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13043 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13043 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13043 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13043,cell13043,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13043 ⟨39,by decide⟩).lower ∧ (cell13043 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13043 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13043 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13043 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13043 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13043 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13043,cell13043,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13043 ⟨40,by decide⟩).lower ∧ (cell13043 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13043 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13043 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13043 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13043 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13043 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13043,cell13043,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13043 ⟨41,by decide⟩).lower ∧ (cell13043 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13043 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13043 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13043 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13043 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13043 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13043,cell13043,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13043 ⟨42,by decide⟩).lower ∧ (cell13043 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13043 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13043 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13043 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13043 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13043 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13043,cell13043,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13043 ⟨43,by decide⟩).lower ∧ (cell13043 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13043 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13043 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13043 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13043 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13043 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13043,cell13043,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13043 ⟨44,by decide⟩).lower ∧ (cell13043 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13043 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13043 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13043 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13043 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13043 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13043,cell13043,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13043 ⟨45,by decide⟩).lower ∧ (cell13043 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13043 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13043 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13043 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13043 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13043 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13043,cell13043,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13043 ⟨46,by decide⟩).lower ∧ (cell13043 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13043 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13043 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13043 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13043 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13043 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13043,cell13043,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13043 ⟨47,by decide⟩).lower ∧ (cell13043 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13043 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13043 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13043 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13043 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13043 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13043,cell13043,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13043 ⟨48,by decide⟩).lower ∧ (cell13043 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13043 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13043 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13043 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13043 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13043 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13043,cell13043,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13043 ⟨49,by decide⟩).lower ∧ (cell13043 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13043 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13043 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13043 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13043 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13043 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13043,cell13043,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13043 ⟨50,by decide⟩).lower ∧ (cell13043 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13043 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13043 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13043 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13043 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13043 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13043,cell13043,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13043 ⟨51,by decide⟩).lower ∧ (cell13043 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13043 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13043 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13043 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13043 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13043 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13043,cell13043,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13043 ⟨52,by decide⟩).lower ∧ (cell13043 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13043 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13043 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13043 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13043 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13043 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13043,cell13043,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13043 i).lower ∧
    (cell13043 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13043 i).upper ≤ (0.532 : ℝ) ∧
    (cell13043 i).centre ≤ (0.1 : ℝ) ∧ (cell13043 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13043 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13043 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13043

/-! The local source numeric instances at 13043 have no network premises. -/
namespace BstLean.Part269.N13043
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13043)
open BstLean.Part268 (cell13043)

noncomputable def sourceNumerics13043 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13043 (cell13043 i)
      scalarRow13043.M scalarRow13043.H scalarRow13043.xi := by
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
    energy_allowance := scalarRow13043.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13043]
    centre_nonneg := (scalarRow13043.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D27.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13043])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13043
/-! Actual 13044 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13044
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13044 ≤ (1.035329755377 : ℝ) := by
  have hr : (114.210332282153 : ℝ) ≤ √(13044 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.210332282153 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13044 13044 (11 / 1000) ≤
    (0.008369531137 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13044) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.210332282153 : ℝ) ≤ √(13044 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13044)
  have hdiv : K / √(13044 : ℝ) ≤ K / 114.210332282153 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.210332282153 ≤ (0.008369531137 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13044.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13044 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13044 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13044 := gPlus_lower 13044
end BstLean.Part269.N13044

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13044
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035329755376 : ℝ) ≤ wn 13044 := by
  have hn : √(13044 : ℝ) ≤ 114.210332282154 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13044 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.210332282154 ≤ 2 / √(13044 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000245124678 : ℝ) ≤ rhoBar 13044 BstLean.Part154.csC ∧
    rhoBar 13044 BstLean.Part154.csC ≤ 0.000245125058 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035329755376 : ℝ) / (1.295212 * 13044) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035329755377 : ℝ) / (1.29521 * 13044) := by gcongr
      _ ≤ (0.000245125058 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13044 BstLean.Part154.csC) ≤ 0.000980560319 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13044 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13044 BstLean.Part154.csC) (piBar (rhoBar 13044 BstLean.Part154.csC)) ≤ 0.000187227939 ∧
    cc1 (rhoBar 13044 BstLean.Part154.csC) (piBar (rhoBar 13044 BstLean.Part154.csC)) ≤ 0.000119134429 ∧
    cc2 (rhoBar 13044 BstLean.Part154.csC) ≤ 0.000069158507 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13044 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13044 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13044 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13044 BstLean.Part154.csC * nuR (rhoBar 13044 BstLean.Part154.csC)) ≤ 0.000490265138 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000245125058 : ℝ) * 0.000980560319 := by gcongr
      _ ≤ (0.000490265138 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13044 BstLean.Part154.csC) * nuR (rhoBar 13044 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000980560319 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13044 BstLean.Part154.csC) * rhoBar 13044 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000245125058 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000245125058 / 2 + 0.399 * 0.000980560319 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000187227939 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000490265138 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119134429 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000245125058 / 1.414213562 := by gcongr
      _ ≤ (0.000069158507 : ℝ) := by norm_num

end BstLean.Part269.N13044

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13044
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13044 BstLean.Part154.csC) (piBar (rhoBar 13044 BstLean.Part154.csC)) ≤ 1.51383E-7 := by
  have hr0 : 0 ≤ rhoBar 13044 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13044 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13044 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13044 BstLean.Part154.csC) (piBar (rhoBar 13044 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13044 BstLean.Part154.csC) (piBar (rhoBar 13044 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13044 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000187227939 : ℝ) ^ 2 + 0.000119134429 ^ 2 + 3 * 0.000069158507 ^ 2 +
        2 * 0.797885 * 0.000187227939 * 0.000119134429 + 2 * 0.000187227939 * 0.000069158507 +
        4 * 0.797885 * 0.000119134429 * 0.000069158507 := by gcongr
    _ ≤ (1.51383E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13044 BstLean.Part154.csC Θ ≤ 0.002557577241 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13044 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13044 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13044 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13044 BstLean.Part154.csC) (piBar (rhoBar 13044 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13044 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035329755377 * 1.51383E-7 / (0.000245124678 : ℝ) := by gcongr
    _ ≤ 0.002557577241 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13044 BstLean.Part154.csC Θ ≤ 0.002836453823 + 0.000646259009 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13044 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13044 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13044 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035329755377 : ℝ) * ((2 * Θ * 0.000245125058 +
        (6863 / 10000) * 0.000245125058 * 13044 * 0.000980560319) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002836453823 + 0.000646259009 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13044 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13044 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13044 0.011 Θ ∧ gammaRatio 13044 0.011 Θ ≤ 0.000084267656 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13044 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035329755377 : ℝ) * 0.525 / ((1 - 0.011) * 13044) := by gcongr
      _ ≤ (0.000084267656 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13044 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13044 0.011 Θ) :=
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
    badAllowance 13044 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000383431726 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13044 BstLean.Part154.csC) 1.22 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 2 (rhoBar 13044 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13044 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13044 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13044 0.011 Θ) 1.12 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 1 (gammaRatio 13044 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13044 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13044 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13044 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13044 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035329755377 : ℝ) * 13044 *
        (1.3781E-8 / 1.1045361 + 1.6832E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000383431726 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13044 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003219885549 + 0.003203836250 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13044

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13044
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13044 BstLean.Part154.csC) (piBar (rhoBar 13044 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13044 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13044 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13044 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13044 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13044 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13044 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13044 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13044 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13044 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13044 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13044 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13044 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13044 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13044 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051780169082 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13044) ≤ 0.010456475848 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13044 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035329755377)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010456475848 + 2 * 0.737676 / 13044) := by gcongr
    _ ≤ (0.051780169082 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13044 12 ≤ 0.0015 := by
  exact BstLean.Part269.S27.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13044

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13044
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560518714727 : ℝ) ≤ plow 13044 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13044) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052408499581)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001342728052) : eMP 13044 0.011 xi bn ≤ 0.001156418849 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13044 : ℝ) * (1 - 0.011))) ≤ 0.000571828045 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001342728052 / (13044 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000571828045 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000571828045 : ℝ) + 3.141593 * 0.052408499581 / (13044 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001156418849 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052408499581)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001342728052) : PiBarMP 13044 12 0.011 xi bn ≤ 0.159089431558 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13044 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036643253841 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.580438456628 : ℝ) ≤ √((13044 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.210332282153 : ℝ) ≤ √(13044 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13044) ≤ 0.121989035356 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036643253841 + 0.052408499581 * 1.772454 / (2 * (113.580438456628 : ℝ))) * (1 + 0.001156418849) +
        8 / (13044 * 114.210332282153) + 0.121989035356 := by gcongr
    _ ≤ (0.159089431558 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052408499581)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001342728052) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280709196471) :
    parallelOracle 13044 0.011 xi bn cd ≤ 0.160053671247 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13044 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13044 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560518714727 : ℝ) ≤ plow 13044 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.210332282153 : ℝ) ≤ √(13044 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280709196471 : ℝ) / (2 * 0.560518714727 * 114.210332282153)) * 0.159089431558 +
        0.280709196471 ^ 2 / (2 * 0.560518714727 * 114.210332282153) := by gcongr
    _ ≤ (0.160053671247 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052408499581) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001342728052)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280709196471) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13044 13044 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560518714727 : ℝ) ≤ plow 13044 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.210332282153 : ℝ) ≤ √(13044 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13044 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13044 Θ 1.22 ≤ 0.011611037929 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.210332282153 := by gcongr <;> linarith
      _ ≤ (0.011611037929 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13044 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13044 13044 0.011 ≤ 0.008369531137 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13044 13044 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13044 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13044 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13044 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13044 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160053671247 + 0.011611037929 + (0.008369531137 : ℝ) *
        (1 + 2 * (0.280709196471 + 0.011611037929) / (0.560518714727 * 114.210332282153))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13044]

end BstLean.Part269.N13044

/-! The original eight local profiles supply actual 13044 moment certificates. -/
namespace BstLean.Part269.N13044
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13044 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13044 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13044 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052408499581 ∧
    0 ≤ bN 13044 BstLean.Part154.csC (groupTheta g) ∧ bN 13044 BstLean.Part154.csC (groupTheta g) ≤ 0.001342728052 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13044 13044 0.011
      (momentAllowance 13044 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13044 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13044 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13044 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13044 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13044 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228929027389 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13044 0.011
      (momentAllowance 13044 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13044 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13044
/-! The actual computed-centre upper energy formula at 13044. -/
namespace BstLean.Part269.N13044
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13044

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13044
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13044)
open BstLean.Part268 (cell13044)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084545667069
  | 2 => 0.085472846782
  | 3 => 0.086396010631
  | 4 => 0.087316070150
  | 5 => 0.088234142633
  | 6 => 0.089151583512
  | 7 => 0.090070022140
  | 8 => 0.090991401056
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13044 13044 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13044 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N13044

/-! Actual upper energy certificates on all 43 source endpoints at 13044. -/
namespace BstLean.Part269.N13044
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13044)
open BstLean.Part268 (cell13044)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13044 (gMinus 13044) (1 - (cell13044 i).lower) ≤ 1 ∧
    energyUpper 13044 (gMinus 13044) (BstLean.Part211.gPlus 13044)
      (finiteEnergy 13044 13044 0.011) (1 - (cell13044 i).lower) ≤
      (cell13044 i).energy := by
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
      have E := BstLean.Part269.S27.uniformEnergy10 (n := 13044) (by norm_num)
        (q := 1 - (cell13044 ⟨10,by decide⟩).lower)
        (by norm_num [cell13044]) (by norm_num [cell13044])
      exact ⟨E.1,E.2.trans (by norm_num [cell13044])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy11 (n := 13044) (by norm_num)
        (q := 1 - (cell13044 ⟨11,by decide⟩).lower)
        (by norm_num [cell13044]) (by norm_num [cell13044])
      exact ⟨E.1,E.2.trans (by norm_num [cell13044])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy12 (n := 13044) (by norm_num)
        (q := 1 - (cell13044 ⟨12,by decide⟩).lower)
        (by norm_num [cell13044]) (by norm_num [cell13044])
      exact ⟨E.1,E.2.trans (by norm_num [cell13044])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy13 (n := 13044) (by norm_num)
        (q := 1 - (cell13044 ⟨13,by decide⟩).lower)
        (by norm_num [cell13044]) (by norm_num [cell13044])
      exact ⟨E.1,E.2.trans (by norm_num [cell13044])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy14 (n := 13044) (by norm_num)
        (q := 1 - (cell13044 ⟨14,by decide⟩).lower)
        (by norm_num [cell13044]) (by norm_num [cell13044])
      exact ⟨E.1,E.2.trans (by norm_num [cell13044])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy15 (n := 13044) (by norm_num)
        (q := 1 - (cell13044 ⟨15,by decide⟩).lower)
        (by norm_num [cell13044]) (by norm_num [cell13044])
      exact ⟨E.1,E.2.trans (by norm_num [cell13044])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy16 (n := 13044) (by norm_num)
        (q := 1 - (cell13044 ⟨16,by decide⟩).lower)
        (by norm_num [cell13044]) (by norm_num [cell13044])
      exact ⟨E.1,E.2.trans (by norm_num [cell13044])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy17 (n := 13044) (by norm_num)
        (q := 1 - (cell13044 ⟨17,by decide⟩).lower)
        (by norm_num [cell13044]) (by norm_num [cell13044])
      exact ⟨E.1,E.2.trans (by norm_num [cell13044])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy18 (n := 13044) (by norm_num)
        (q := 1 - (cell13044 ⟨18,by decide⟩).lower)
        (by norm_num [cell13044]) (by norm_num [cell13044])
      exact ⟨E.1,E.2.trans (by norm_num [cell13044])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy19 (n := 13044) (by norm_num)
        (q := 1 - (cell13044 ⟨19,by decide⟩).lower)
        (by norm_num [cell13044]) (by norm_num [cell13044])
      exact ⟨E.1,E.2.trans (by norm_num [cell13044])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy20 (n := 13044) (by norm_num)
        (q := 1 - (cell13044 ⟨20,by decide⟩).lower)
        (by norm_num [cell13044]) (by norm_num [cell13044])
      exact ⟨E.1,E.2.trans (by norm_num [cell13044])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy21 (n := 13044) (by norm_num)
        (q := 1 - (cell13044 ⟨21,by decide⟩).lower)
        (by norm_num [cell13044]) (by norm_num [cell13044])
      exact ⟨E.1,E.2.trans (by norm_num [cell13044])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy22 (n := 13044) (by norm_num)
        (q := 1 - (cell13044 ⟨22,by decide⟩).lower)
        (by norm_num [cell13044]) (by norm_num [cell13044])
      exact ⟨E.1,E.2.trans (by norm_num [cell13044])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy23 (n := 13044) (by norm_num)
        (q := 1 - (cell13044 ⟨23,by decide⟩).lower)
        (by norm_num [cell13044]) (by norm_num [cell13044])
      exact ⟨E.1,E.2.trans (by norm_num [cell13044])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy24 (n := 13044) (by norm_num)
        (q := 1 - (cell13044 ⟨24,by decide⟩).lower)
        (by norm_num [cell13044]) (by norm_num [cell13044])
      exact ⟨E.1,E.2.trans (by norm_num [cell13044])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy25 (n := 13044) (by norm_num)
        (q := 1 - (cell13044 ⟨25,by decide⟩).lower)
        (by norm_num [cell13044]) (by norm_num [cell13044])
      exact ⟨E.1,E.2.trans (by norm_num [cell13044])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy26 (n := 13044) (by norm_num)
        (q := 1 - (cell13044 ⟨26,by decide⟩).lower)
        (by norm_num [cell13044]) (by norm_num [cell13044])
      exact ⟨E.1,E.2.trans (by norm_num [cell13044])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy27 (n := 13044) (by norm_num)
        (q := 1 - (cell13044 ⟨27,by decide⟩).lower)
        (by norm_num [cell13044]) (by norm_num [cell13044])
      exact ⟨E.1,E.2.trans (by norm_num [cell13044])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy28 (n := 13044) (by norm_num)
        (q := 1 - (cell13044 ⟨28,by decide⟩).lower)
        (by norm_num [cell13044]) (by norm_num [cell13044])
      exact ⟨E.1,E.2.trans (by norm_num [cell13044])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy29 (n := 13044) (by norm_num)
        (q := 1 - (cell13044 ⟨29,by decide⟩).lower)
        (by norm_num [cell13044]) (by norm_num [cell13044])
      exact ⟨E.1,E.2.trans (by norm_num [cell13044])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy30 (n := 13044) (by norm_num)
        (q := 1 - (cell13044 ⟨30,by decide⟩).lower)
        (by norm_num [cell13044]) (by norm_num [cell13044])
      exact ⟨E.1,E.2.trans (by norm_num [cell13044])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy31 (n := 13044) (by norm_num)
        (q := 1 - (cell13044 ⟨31,by decide⟩).lower)
        (by norm_num [cell13044]) (by norm_num [cell13044])
      exact ⟨E.1,E.2.trans (by norm_num [cell13044])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy32 (n := 13044) (by norm_num)
        (q := 1 - (cell13044 ⟨32,by decide⟩).lower)
        (by norm_num [cell13044]) (by norm_num [cell13044])
      exact ⟨E.1,E.2.trans (by norm_num [cell13044])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy33 (n := 13044) (by norm_num)
        (q := 1 - (cell13044 ⟨33,by decide⟩).lower)
        (by norm_num [cell13044]) (by norm_num [cell13044])
      exact ⟨E.1,E.2.trans (by norm_num [cell13044])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy34 (n := 13044) (by norm_num)
        (q := 1 - (cell13044 ⟨34,by decide⟩).lower)
        (by norm_num [cell13044]) (by norm_num [cell13044])
      exact ⟨E.1,E.2.trans (by norm_num [cell13044])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy35 (n := 13044) (by norm_num)
        (q := 1 - (cell13044 ⟨35,by decide⟩).lower)
        (by norm_num [cell13044]) (by norm_num [cell13044])
      exact ⟨E.1,E.2.trans (by norm_num [cell13044])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy36 (n := 13044) (by norm_num)
        (q := 1 - (cell13044 ⟨36,by decide⟩).lower)
        (by norm_num [cell13044]) (by norm_num [cell13044])
      exact ⟨E.1,E.2.trans (by norm_num [cell13044])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy37 (n := 13044) (by norm_num)
        (q := 1 - (cell13044 ⟨37,by decide⟩).lower)
        (by norm_num [cell13044]) (by norm_num [cell13044])
      exact ⟨E.1,E.2.trans (by norm_num [cell13044])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy38 (n := 13044) (by norm_num)
        (q := 1 - (cell13044 ⟨38,by decide⟩).lower)
        (by norm_num [cell13044]) (by norm_num [cell13044])
      exact ⟨E.1,E.2.trans (by norm_num [cell13044])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy39 (n := 13044) (by norm_num)
        (q := 1 - (cell13044 ⟨39,by decide⟩).lower)
        (by norm_num [cell13044]) (by norm_num [cell13044])
      exact ⟨E.1,E.2.trans (by norm_num [cell13044])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy40 (n := 13044) (by norm_num)
        (q := 1 - (cell13044 ⟨40,by decide⟩).lower)
        (by norm_num [cell13044]) (by norm_num [cell13044])
      exact ⟨E.1,E.2.trans (by norm_num [cell13044])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy41 (n := 13044) (by norm_num)
        (q := 1 - (cell13044 ⟨41,by decide⟩).lower)
        (by norm_num [cell13044]) (by norm_num [cell13044])
      exact ⟨E.1,E.2.trans (by norm_num [cell13044])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy42 (n := 13044) (by norm_num)
        (q := 1 - (cell13044 ⟨42,by decide⟩).lower)
        (by norm_num [cell13044]) (by norm_num [cell13044])
      exact ⟨E.1,E.2.trans (by norm_num [cell13044])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy43 (n := 13044) (by norm_num)
        (q := 1 - (cell13044 ⟨43,by decide⟩).lower)
        (by norm_num [cell13044]) (by norm_num [cell13044])
      exact ⟨E.1,E.2.trans (by norm_num [cell13044])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy44 (n := 13044) (by norm_num)
        (q := 1 - (cell13044 ⟨44,by decide⟩).lower)
        (by norm_num [cell13044]) (by norm_num [cell13044])
      exact ⟨E.1,E.2.trans (by norm_num [cell13044])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy45 (n := 13044) (by norm_num)
        (q := 1 - (cell13044 ⟨45,by decide⟩).lower)
        (by norm_num [cell13044]) (by norm_num [cell13044])
      exact ⟨E.1,E.2.trans (by norm_num [cell13044])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy46 (n := 13044) (by norm_num)
        (q := 1 - (cell13044 ⟨46,by decide⟩).lower)
        (by norm_num [cell13044]) (by norm_num [cell13044])
      exact ⟨E.1,E.2.trans (by norm_num [cell13044])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy47 (n := 13044) (by norm_num)
        (q := 1 - (cell13044 ⟨47,by decide⟩).lower)
        (by norm_num [cell13044]) (by norm_num [cell13044])
      exact ⟨E.1,E.2.trans (by norm_num [cell13044])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy48 (n := 13044) (by norm_num)
        (q := 1 - (cell13044 ⟨48,by decide⟩).lower)
        (by norm_num [cell13044]) (by norm_num [cell13044])
      exact ⟨E.1,E.2.trans (by norm_num [cell13044])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy49 (n := 13044) (by norm_num)
        (q := 1 - (cell13044 ⟨49,by decide⟩).lower)
        (by norm_num [cell13044]) (by norm_num [cell13044])
      exact ⟨E.1,E.2.trans (by norm_num [cell13044])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy50 (n := 13044) (by norm_num)
        (q := 1 - (cell13044 ⟨50,by decide⟩).lower)
        (by norm_num [cell13044]) (by norm_num [cell13044])
      exact ⟨E.1,E.2.trans (by norm_num [cell13044])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy51 (n := 13044) (by norm_num)
        (q := 1 - (cell13044 ⟨51,by decide⟩).lower)
        (by norm_num [cell13044]) (by norm_num [cell13044])
      exact ⟨E.1,E.2.trans (by norm_num [cell13044])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy52 (n := 13044) (by norm_num)
        (q := 1 - (cell13044 ⟨52,by decide⟩).lower)
        (by norm_num [cell13044]) (by norm_num [cell13044])
      exact ⟨E.1,E.2.trans (by norm_num [cell13044])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13044

/-! Source-cell containment and simple scalar guards at 13044. -/
namespace BstLean.Part269.N13044
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13044)
open BstLean.Part268 (cell13044)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13044 ⟨10,by decide⟩).lower ∧ (cell13044 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13044 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13044 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13044 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13044 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13044 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13044,cell13044,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13044 ⟨11,by decide⟩).lower ∧ (cell13044 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13044 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13044 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13044 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13044 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13044 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13044,cell13044,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13044 ⟨12,by decide⟩).lower ∧ (cell13044 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13044 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13044 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13044 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13044 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13044 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13044,cell13044,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13044 ⟨13,by decide⟩).lower ∧ (cell13044 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13044 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13044 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13044 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13044 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13044 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13044,cell13044,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13044 ⟨14,by decide⟩).lower ∧ (cell13044 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13044 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13044 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13044 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13044 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13044 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13044,cell13044,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13044 ⟨15,by decide⟩).lower ∧ (cell13044 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13044 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13044 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13044 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13044 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13044 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13044,cell13044,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13044 ⟨16,by decide⟩).lower ∧ (cell13044 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13044 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13044 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13044 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13044 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13044 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13044,cell13044,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13044 ⟨17,by decide⟩).lower ∧ (cell13044 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13044 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13044 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13044 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13044 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13044 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13044,cell13044,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13044 ⟨18,by decide⟩).lower ∧ (cell13044 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13044 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13044 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13044 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13044 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13044 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13044,cell13044,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13044 ⟨19,by decide⟩).lower ∧ (cell13044 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13044 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13044 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13044 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13044 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13044 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13044,cell13044,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13044 ⟨20,by decide⟩).lower ∧ (cell13044 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13044 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13044 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13044 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13044 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13044 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13044,cell13044,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13044 ⟨21,by decide⟩).lower ∧ (cell13044 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13044 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13044 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13044 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13044 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13044 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13044,cell13044,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13044 ⟨22,by decide⟩).lower ∧ (cell13044 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13044 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13044 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13044 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13044 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13044 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13044,cell13044,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13044 ⟨23,by decide⟩).lower ∧ (cell13044 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13044 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13044 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13044 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13044 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13044 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13044,cell13044,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13044 ⟨24,by decide⟩).lower ∧ (cell13044 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13044 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13044 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13044 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13044 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13044 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13044,cell13044,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13044 ⟨25,by decide⟩).lower ∧ (cell13044 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13044 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13044 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13044 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13044 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13044 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13044,cell13044,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13044 ⟨26,by decide⟩).lower ∧ (cell13044 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13044 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13044 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13044 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13044 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13044 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13044,cell13044,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13044 ⟨27,by decide⟩).lower ∧ (cell13044 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13044 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13044 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13044 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13044 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13044 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13044,cell13044,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13044 ⟨28,by decide⟩).lower ∧ (cell13044 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13044 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13044 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13044 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13044 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13044 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13044,cell13044,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13044 ⟨29,by decide⟩).lower ∧ (cell13044 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13044 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13044 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13044 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13044 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13044 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13044,cell13044,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13044 ⟨30,by decide⟩).lower ∧ (cell13044 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13044 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13044 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13044 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13044 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13044 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13044,cell13044,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13044 ⟨31,by decide⟩).lower ∧ (cell13044 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13044 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13044 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13044 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13044 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13044 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13044,cell13044,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13044 ⟨32,by decide⟩).lower ∧ (cell13044 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13044 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13044 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13044 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13044 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13044 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13044,cell13044,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13044 ⟨33,by decide⟩).lower ∧ (cell13044 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13044 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13044 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13044 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13044 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13044 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13044,cell13044,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13044 ⟨34,by decide⟩).lower ∧ (cell13044 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13044 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13044 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13044 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13044 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13044 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13044,cell13044,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13044 ⟨35,by decide⟩).lower ∧ (cell13044 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13044 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13044 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13044 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13044 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13044 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13044,cell13044,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13044 ⟨36,by decide⟩).lower ∧ (cell13044 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13044 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13044 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13044 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13044 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13044 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13044,cell13044,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13044 ⟨37,by decide⟩).lower ∧ (cell13044 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13044 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13044 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13044 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13044 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13044 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13044,cell13044,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13044 ⟨38,by decide⟩).lower ∧ (cell13044 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13044 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13044 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13044 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13044 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13044 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13044,cell13044,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13044 ⟨39,by decide⟩).lower ∧ (cell13044 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13044 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13044 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13044 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13044 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13044 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13044,cell13044,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13044 ⟨40,by decide⟩).lower ∧ (cell13044 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13044 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13044 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13044 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13044 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13044 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13044,cell13044,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13044 ⟨41,by decide⟩).lower ∧ (cell13044 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13044 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13044 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13044 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13044 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13044 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13044,cell13044,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13044 ⟨42,by decide⟩).lower ∧ (cell13044 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13044 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13044 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13044 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13044 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13044 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13044,cell13044,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13044 ⟨43,by decide⟩).lower ∧ (cell13044 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13044 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13044 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13044 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13044 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13044 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13044,cell13044,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13044 ⟨44,by decide⟩).lower ∧ (cell13044 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13044 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13044 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13044 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13044 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13044 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13044,cell13044,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13044 ⟨45,by decide⟩).lower ∧ (cell13044 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13044 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13044 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13044 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13044 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13044 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13044,cell13044,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13044 ⟨46,by decide⟩).lower ∧ (cell13044 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13044 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13044 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13044 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13044 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13044 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13044,cell13044,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13044 ⟨47,by decide⟩).lower ∧ (cell13044 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13044 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13044 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13044 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13044 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13044 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13044,cell13044,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13044 ⟨48,by decide⟩).lower ∧ (cell13044 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13044 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13044 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13044 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13044 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13044 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13044,cell13044,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13044 ⟨49,by decide⟩).lower ∧ (cell13044 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13044 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13044 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13044 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13044 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13044 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13044,cell13044,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13044 ⟨50,by decide⟩).lower ∧ (cell13044 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13044 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13044 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13044 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13044 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13044 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13044,cell13044,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13044 ⟨51,by decide⟩).lower ∧ (cell13044 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13044 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13044 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13044 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13044 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13044 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13044,cell13044,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13044 ⟨52,by decide⟩).lower ∧ (cell13044 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13044 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13044 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13044 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13044 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13044 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13044,cell13044,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13044 i).lower ∧
    (cell13044 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13044 i).upper ≤ (0.532 : ℝ) ∧
    (cell13044 i).centre ≤ (0.1 : ℝ) ∧ (cell13044 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13044 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13044 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13044

/-! The local source numeric instances at 13044 have no network premises. -/
namespace BstLean.Part269.N13044
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13044)
open BstLean.Part268 (cell13044)

noncomputable def sourceNumerics13044 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13044 (cell13044 i)
      scalarRow13044.M scalarRow13044.H scalarRow13044.xi := by
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
    energy_allowance := scalarRow13044.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13044]
    centre_nonneg := (scalarRow13044.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D27.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13044])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13044
/-! Actual 13045 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13045
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13045 ≤ (1.035328389448 : ℝ) := by
  have hr : (114.214710085872 : ℝ) ≤ √(13045 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.214710085872 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13045 13045 (11 / 1000) ≤
    (0.008369210334 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13045) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.214710085872 : ℝ) ≤ √(13045 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13045)
  have hdiv : K / √(13045 : ℝ) ≤ K / 114.214710085872 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.214710085872 ≤ (0.008369210334 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13045.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13045 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13045 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13045 := gPlus_lower 13045
end BstLean.Part269.N13045

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13045
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035328389447 : ℝ) ≤ wn 13045 := by
  have hn : √(13045 : ℝ) ≤ 114.214710085873 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13045 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.214710085873 ≤ 2 / √(13045 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000245105564 : ℝ) ≤ rhoBar 13045 BstLean.Part154.csC ∧
    rhoBar 13045 BstLean.Part154.csC ≤ 0.000245105944 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035328389447 : ℝ) / (1.295212 * 13045) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035328389448 : ℝ) / (1.29521 * 13045) := by gcongr
      _ ≤ (0.000245105944 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13045 BstLean.Part154.csC) ≤ 0.000980483853 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13045 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13045 BstLean.Part154.csC) (piBar (rhoBar 13045 BstLean.Part154.csC)) ≤ 0.000187213339 ∧
    cc1 (rhoBar 13045 BstLean.Part154.csC) (piBar (rhoBar 13045 BstLean.Part154.csC)) ≤ 0.000119125139 ∧
    cc2 (rhoBar 13045 BstLean.Part154.csC) ≤ 0.000069153114 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13045 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13045 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13045 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13045 BstLean.Part154.csC * nuR (rhoBar 13045 BstLean.Part154.csC)) ≤ 0.000490226908 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000245105944 : ℝ) * 0.000980483853 := by gcongr
      _ ≤ (0.000490226908 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13045 BstLean.Part154.csC) * nuR (rhoBar 13045 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000980483853 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13045 BstLean.Part154.csC) * rhoBar 13045 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000245105944 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000245105944 / 2 + 0.399 * 0.000980483853 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000187213339 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000490226908 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119125139 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000245105944 / 1.414213562 := by gcongr
      _ ≤ (0.000069153114 : ℝ) := by norm_num

end BstLean.Part269.N13045

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13045
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13045 BstLean.Part154.csC) (piBar (rhoBar 13045 BstLean.Part154.csC)) ≤ 1.51359E-7 := by
  have hr0 : 0 ≤ rhoBar 13045 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13045 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13045 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13045 BstLean.Part154.csC) (piBar (rhoBar 13045 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13045 BstLean.Part154.csC) (piBar (rhoBar 13045 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13045 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000187213339 : ℝ) ^ 2 + 0.000119125139 ^ 2 + 3 * 0.000069153114 ^ 2 +
        2 * 0.797885 * 0.000187213339 * 0.000119125139 + 2 * 0.000187213339 * 0.000069153114 +
        4 * 0.797885 * 0.000119125139 * 0.000069153114 := by gcongr
    _ ≤ (1.51359E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13045 BstLean.Part154.csC Θ ≤ 0.002557367808 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13045 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13045 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13045 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13045 BstLean.Part154.csC) (piBar (rhoBar 13045 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13045 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035328389448 * 1.51359E-7 / (0.000245105564 : ℝ) := by gcongr
    _ ≤ 0.002557367808 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13045 BstLean.Part154.csC Θ ≤ 0.002836225148 + 0.000646207763 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13045 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13045 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13045 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035328389448 : ℝ) * ((2 * Θ * 0.000245105944 +
        (6863 / 10000) * 0.000245105944 * 13045 * 0.000980483853) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002836225148 + 0.000646207763 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13045 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13045 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13045 0.011 Θ ∧ gammaRatio 13045 0.011 Θ ≤ 0.000084261085 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13045 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035328389448 : ℝ) * 0.525 / ((1 - 0.011) * 13045) := by gcongr
      _ ≤ (0.000084261085 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13045 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13045 0.011 Θ) :=
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
    badAllowance 13045 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000383431726 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13045 BstLean.Part154.csC) 1.22 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 2 (rhoBar 13045 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13045 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13045 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13045 0.011 Θ) 1.12 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 1 (gammaRatio 13045 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13045 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13045 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13045 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13045 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035328389448 : ℝ) * 13045 *
        (1.3781E-8 / 1.1045361 + 1.6832E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000383431726 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13045 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003219656874 + 0.003203575571 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13045

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13045
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13045 BstLean.Part154.csC) (piBar (rhoBar 13045 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13045 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13045 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13045 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13045 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13045 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13045 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13045 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13045 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13045 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13045 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13045 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13045 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13045 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13045 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051778163133 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13045) ≤ 0.010456075056 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13045 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035328389448)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010456075056 + 2 * 0.737676 / 13045) := by gcongr
    _ ≤ (0.051778163133 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13045 12 ≤ 0.0015 := by
  exact BstLean.Part269.S27.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13045

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13045
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560518757592 : ℝ) ≤ plow 13045 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13045) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052408134049)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001342618100) : eMP 13045 0.011 xi bn ≤ 0.001156327120 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13045 : ℝ) * (1 - 0.011))) ≤ 0.000571782714 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001342618100 / (13045 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000571782714 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000571782714 : ℝ) + 3.141593 * 0.052408134049 / (13045 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001156327120 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052408134049)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001342618100) : PiBarMP 13045 12 0.011 xi bn ≤ 0.159083231136 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13045 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036641753507 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.584792115846 : ℝ) ≤ √((13045 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.214710085872 : ℝ) ≤ √(13045 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13045) ≤ 0.121984359566 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036641753507 + 0.052408134049 * 1.772454 / (2 * (113.584792115846 : ℝ))) * (1 + 0.001156327120) +
        8 / (13045 * 114.214710085872) + 0.121984359566 := by gcongr
    _ ≤ (0.159083231136 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052408134049)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001342618100) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280706392168) :
    parallelOracle 13045 0.011 xi bn cd ≤ 0.160047404418 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13045 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13045 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560518757592 : ℝ) ≤ plow 13045 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.214710085872 : ℝ) ≤ √(13045 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280706392168 : ℝ) / (2 * 0.560518757592 * 114.214710085872)) * 0.159083231136 +
        0.280706392168 ^ 2 / (2 * 0.560518757592 * 114.214710085872) := by gcongr
    _ ≤ (0.160047404418 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052408134049) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001342618100)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280706392168) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13045 13045 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560518757592 : ℝ) ≤ plow 13045 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.214710085872 : ℝ) ≤ √(13045 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13045 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13045 Θ 1.22 ≤ 0.011610592883 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.214710085872 := by gcongr <;> linarith
      _ ≤ (0.011610592883 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13045 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13045 13045 0.011 ≤ 0.008369210334 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13045 13045 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13045 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13045 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13045 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13045 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160047404418 + 0.011610592883 + (0.008369210334 : ℝ) *
        (1 + 2 * (0.280706392168 + 0.011610592883) / (0.560518757592 * 114.214710085872))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13045]

end BstLean.Part269.N13045

/-! The original eight local profiles supply actual 13045 moment certificates. -/
namespace BstLean.Part269.N13045
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13045 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13045 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13045 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052408134049 ∧
    0 ≤ bN 13045 BstLean.Part154.csC (groupTheta g) ∧ bN 13045 BstLean.Part154.csC (groupTheta g) ≤ 0.001342618100 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13045 13045 0.011
      (momentAllowance 13045 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13045 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13045 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13045 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13045 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13045 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228928229035 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13045 0.011
      (momentAllowance 13045 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13045 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13045
/-! The actual computed-centre upper energy formula at 13045. -/
namespace BstLean.Part269.N13045
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13045

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13045
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13045)
open BstLean.Part268 (cell13045)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084543083666
  | 2 => 0.085470230051
  | 3 => 0.086393355610
  | 4 => 0.087313370708
  | 5 => 0.088231391253
  | 6 => 0.089148771053
  | 7 => 0.090067137557
  | 8 => 0.090988431100
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13045 13045 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13045 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N13045

/-! Actual upper energy certificates on all 43 source endpoints at 13045. -/
namespace BstLean.Part269.N13045
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13045)
open BstLean.Part268 (cell13045)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13045 (gMinus 13045) (1 - (cell13045 i).lower) ≤ 1 ∧
    energyUpper 13045 (gMinus 13045) (BstLean.Part211.gPlus 13045)
      (finiteEnergy 13045 13045 0.011) (1 - (cell13045 i).lower) ≤
      (cell13045 i).energy := by
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
      have E := BstLean.Part269.S27.uniformEnergy10 (n := 13045) (by norm_num)
        (q := 1 - (cell13045 ⟨10,by decide⟩).lower)
        (by norm_num [cell13045]) (by norm_num [cell13045])
      exact ⟨E.1,E.2.trans (by norm_num [cell13045])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy11 (n := 13045) (by norm_num)
        (q := 1 - (cell13045 ⟨11,by decide⟩).lower)
        (by norm_num [cell13045]) (by norm_num [cell13045])
      exact ⟨E.1,E.2.trans (by norm_num [cell13045])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy12 (n := 13045) (by norm_num)
        (q := 1 - (cell13045 ⟨12,by decide⟩).lower)
        (by norm_num [cell13045]) (by norm_num [cell13045])
      exact ⟨E.1,E.2.trans (by norm_num [cell13045])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy13 (n := 13045) (by norm_num)
        (q := 1 - (cell13045 ⟨13,by decide⟩).lower)
        (by norm_num [cell13045]) (by norm_num [cell13045])
      exact ⟨E.1,E.2.trans (by norm_num [cell13045])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy14 (n := 13045) (by norm_num)
        (q := 1 - (cell13045 ⟨14,by decide⟩).lower)
        (by norm_num [cell13045]) (by norm_num [cell13045])
      exact ⟨E.1,E.2.trans (by norm_num [cell13045])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy15 (n := 13045) (by norm_num)
        (q := 1 - (cell13045 ⟨15,by decide⟩).lower)
        (by norm_num [cell13045]) (by norm_num [cell13045])
      exact ⟨E.1,E.2.trans (by norm_num [cell13045])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy16 (n := 13045) (by norm_num)
        (q := 1 - (cell13045 ⟨16,by decide⟩).lower)
        (by norm_num [cell13045]) (by norm_num [cell13045])
      exact ⟨E.1,E.2.trans (by norm_num [cell13045])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy17 (n := 13045) (by norm_num)
        (q := 1 - (cell13045 ⟨17,by decide⟩).lower)
        (by norm_num [cell13045]) (by norm_num [cell13045])
      exact ⟨E.1,E.2.trans (by norm_num [cell13045])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy18 (n := 13045) (by norm_num)
        (q := 1 - (cell13045 ⟨18,by decide⟩).lower)
        (by norm_num [cell13045]) (by norm_num [cell13045])
      exact ⟨E.1,E.2.trans (by norm_num [cell13045])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy19 (n := 13045) (by norm_num)
        (q := 1 - (cell13045 ⟨19,by decide⟩).lower)
        (by norm_num [cell13045]) (by norm_num [cell13045])
      exact ⟨E.1,E.2.trans (by norm_num [cell13045])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy20 (n := 13045) (by norm_num)
        (q := 1 - (cell13045 ⟨20,by decide⟩).lower)
        (by norm_num [cell13045]) (by norm_num [cell13045])
      exact ⟨E.1,E.2.trans (by norm_num [cell13045])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy21 (n := 13045) (by norm_num)
        (q := 1 - (cell13045 ⟨21,by decide⟩).lower)
        (by norm_num [cell13045]) (by norm_num [cell13045])
      exact ⟨E.1,E.2.trans (by norm_num [cell13045])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy22 (n := 13045) (by norm_num)
        (q := 1 - (cell13045 ⟨22,by decide⟩).lower)
        (by norm_num [cell13045]) (by norm_num [cell13045])
      exact ⟨E.1,E.2.trans (by norm_num [cell13045])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy23 (n := 13045) (by norm_num)
        (q := 1 - (cell13045 ⟨23,by decide⟩).lower)
        (by norm_num [cell13045]) (by norm_num [cell13045])
      exact ⟨E.1,E.2.trans (by norm_num [cell13045])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy24 (n := 13045) (by norm_num)
        (q := 1 - (cell13045 ⟨24,by decide⟩).lower)
        (by norm_num [cell13045]) (by norm_num [cell13045])
      exact ⟨E.1,E.2.trans (by norm_num [cell13045])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy25 (n := 13045) (by norm_num)
        (q := 1 - (cell13045 ⟨25,by decide⟩).lower)
        (by norm_num [cell13045]) (by norm_num [cell13045])
      exact ⟨E.1,E.2.trans (by norm_num [cell13045])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy26 (n := 13045) (by norm_num)
        (q := 1 - (cell13045 ⟨26,by decide⟩).lower)
        (by norm_num [cell13045]) (by norm_num [cell13045])
      exact ⟨E.1,E.2.trans (by norm_num [cell13045])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy27 (n := 13045) (by norm_num)
        (q := 1 - (cell13045 ⟨27,by decide⟩).lower)
        (by norm_num [cell13045]) (by norm_num [cell13045])
      exact ⟨E.1,E.2.trans (by norm_num [cell13045])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy28 (n := 13045) (by norm_num)
        (q := 1 - (cell13045 ⟨28,by decide⟩).lower)
        (by norm_num [cell13045]) (by norm_num [cell13045])
      exact ⟨E.1,E.2.trans (by norm_num [cell13045])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy29 (n := 13045) (by norm_num)
        (q := 1 - (cell13045 ⟨29,by decide⟩).lower)
        (by norm_num [cell13045]) (by norm_num [cell13045])
      exact ⟨E.1,E.2.trans (by norm_num [cell13045])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy30 (n := 13045) (by norm_num)
        (q := 1 - (cell13045 ⟨30,by decide⟩).lower)
        (by norm_num [cell13045]) (by norm_num [cell13045])
      exact ⟨E.1,E.2.trans (by norm_num [cell13045])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy31 (n := 13045) (by norm_num)
        (q := 1 - (cell13045 ⟨31,by decide⟩).lower)
        (by norm_num [cell13045]) (by norm_num [cell13045])
      exact ⟨E.1,E.2.trans (by norm_num [cell13045])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy32 (n := 13045) (by norm_num)
        (q := 1 - (cell13045 ⟨32,by decide⟩).lower)
        (by norm_num [cell13045]) (by norm_num [cell13045])
      exact ⟨E.1,E.2.trans (by norm_num [cell13045])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy33 (n := 13045) (by norm_num)
        (q := 1 - (cell13045 ⟨33,by decide⟩).lower)
        (by norm_num [cell13045]) (by norm_num [cell13045])
      exact ⟨E.1,E.2.trans (by norm_num [cell13045])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy34 (n := 13045) (by norm_num)
        (q := 1 - (cell13045 ⟨34,by decide⟩).lower)
        (by norm_num [cell13045]) (by norm_num [cell13045])
      exact ⟨E.1,E.2.trans (by norm_num [cell13045])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy35 (n := 13045) (by norm_num)
        (q := 1 - (cell13045 ⟨35,by decide⟩).lower)
        (by norm_num [cell13045]) (by norm_num [cell13045])
      exact ⟨E.1,E.2.trans (by norm_num [cell13045])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy36 (n := 13045) (by norm_num)
        (q := 1 - (cell13045 ⟨36,by decide⟩).lower)
        (by norm_num [cell13045]) (by norm_num [cell13045])
      exact ⟨E.1,E.2.trans (by norm_num [cell13045])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy37 (n := 13045) (by norm_num)
        (q := 1 - (cell13045 ⟨37,by decide⟩).lower)
        (by norm_num [cell13045]) (by norm_num [cell13045])
      exact ⟨E.1,E.2.trans (by norm_num [cell13045])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy38 (n := 13045) (by norm_num)
        (q := 1 - (cell13045 ⟨38,by decide⟩).lower)
        (by norm_num [cell13045]) (by norm_num [cell13045])
      exact ⟨E.1,E.2.trans (by norm_num [cell13045])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy39 (n := 13045) (by norm_num)
        (q := 1 - (cell13045 ⟨39,by decide⟩).lower)
        (by norm_num [cell13045]) (by norm_num [cell13045])
      exact ⟨E.1,E.2.trans (by norm_num [cell13045])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy40 (n := 13045) (by norm_num)
        (q := 1 - (cell13045 ⟨40,by decide⟩).lower)
        (by norm_num [cell13045]) (by norm_num [cell13045])
      exact ⟨E.1,E.2.trans (by norm_num [cell13045])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy41 (n := 13045) (by norm_num)
        (q := 1 - (cell13045 ⟨41,by decide⟩).lower)
        (by norm_num [cell13045]) (by norm_num [cell13045])
      exact ⟨E.1,E.2.trans (by norm_num [cell13045])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy42 (n := 13045) (by norm_num)
        (q := 1 - (cell13045 ⟨42,by decide⟩).lower)
        (by norm_num [cell13045]) (by norm_num [cell13045])
      exact ⟨E.1,E.2.trans (by norm_num [cell13045])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy43 (n := 13045) (by norm_num)
        (q := 1 - (cell13045 ⟨43,by decide⟩).lower)
        (by norm_num [cell13045]) (by norm_num [cell13045])
      exact ⟨E.1,E.2.trans (by norm_num [cell13045])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy44 (n := 13045) (by norm_num)
        (q := 1 - (cell13045 ⟨44,by decide⟩).lower)
        (by norm_num [cell13045]) (by norm_num [cell13045])
      exact ⟨E.1,E.2.trans (by norm_num [cell13045])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy45 (n := 13045) (by norm_num)
        (q := 1 - (cell13045 ⟨45,by decide⟩).lower)
        (by norm_num [cell13045]) (by norm_num [cell13045])
      exact ⟨E.1,E.2.trans (by norm_num [cell13045])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy46 (n := 13045) (by norm_num)
        (q := 1 - (cell13045 ⟨46,by decide⟩).lower)
        (by norm_num [cell13045]) (by norm_num [cell13045])
      exact ⟨E.1,E.2.trans (by norm_num [cell13045])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy47 (n := 13045) (by norm_num)
        (q := 1 - (cell13045 ⟨47,by decide⟩).lower)
        (by norm_num [cell13045]) (by norm_num [cell13045])
      exact ⟨E.1,E.2.trans (by norm_num [cell13045])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy48 (n := 13045) (by norm_num)
        (q := 1 - (cell13045 ⟨48,by decide⟩).lower)
        (by norm_num [cell13045]) (by norm_num [cell13045])
      exact ⟨E.1,E.2.trans (by norm_num [cell13045])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy49 (n := 13045) (by norm_num)
        (q := 1 - (cell13045 ⟨49,by decide⟩).lower)
        (by norm_num [cell13045]) (by norm_num [cell13045])
      exact ⟨E.1,E.2.trans (by norm_num [cell13045])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy50 (n := 13045) (by norm_num)
        (q := 1 - (cell13045 ⟨50,by decide⟩).lower)
        (by norm_num [cell13045]) (by norm_num [cell13045])
      exact ⟨E.1,E.2.trans (by norm_num [cell13045])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy51 (n := 13045) (by norm_num)
        (q := 1 - (cell13045 ⟨51,by decide⟩).lower)
        (by norm_num [cell13045]) (by norm_num [cell13045])
      exact ⟨E.1,E.2.trans (by norm_num [cell13045])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy52 (n := 13045) (by norm_num)
        (q := 1 - (cell13045 ⟨52,by decide⟩).lower)
        (by norm_num [cell13045]) (by norm_num [cell13045])
      exact ⟨E.1,E.2.trans (by norm_num [cell13045])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13045

/-! Source-cell containment and simple scalar guards at 13045. -/
namespace BstLean.Part269.N13045
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13045)
open BstLean.Part268 (cell13045)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13045 ⟨10,by decide⟩).lower ∧ (cell13045 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13045 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13045 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13045 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13045 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13045 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13045,cell13045,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13045 ⟨11,by decide⟩).lower ∧ (cell13045 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13045 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13045 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13045 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13045 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13045 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13045,cell13045,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13045 ⟨12,by decide⟩).lower ∧ (cell13045 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13045 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13045 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13045 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13045 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13045 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13045,cell13045,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13045 ⟨13,by decide⟩).lower ∧ (cell13045 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13045 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13045 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13045 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13045 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13045 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13045,cell13045,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13045 ⟨14,by decide⟩).lower ∧ (cell13045 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13045 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13045 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13045 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13045 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13045 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13045,cell13045,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13045 ⟨15,by decide⟩).lower ∧ (cell13045 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13045 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13045 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13045 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13045 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13045 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13045,cell13045,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13045 ⟨16,by decide⟩).lower ∧ (cell13045 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13045 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13045 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13045 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13045 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13045 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13045,cell13045,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13045 ⟨17,by decide⟩).lower ∧ (cell13045 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13045 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13045 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13045 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13045 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13045 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13045,cell13045,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13045 ⟨18,by decide⟩).lower ∧ (cell13045 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13045 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13045 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13045 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13045 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13045 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13045,cell13045,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13045 ⟨19,by decide⟩).lower ∧ (cell13045 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13045 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13045 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13045 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13045 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13045 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13045,cell13045,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13045 ⟨20,by decide⟩).lower ∧ (cell13045 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13045 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13045 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13045 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13045 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13045 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13045,cell13045,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13045 ⟨21,by decide⟩).lower ∧ (cell13045 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13045 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13045 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13045 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13045 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13045 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13045,cell13045,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13045 ⟨22,by decide⟩).lower ∧ (cell13045 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13045 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13045 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13045 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13045 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13045 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13045,cell13045,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13045 ⟨23,by decide⟩).lower ∧ (cell13045 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13045 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13045 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13045 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13045 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13045 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13045,cell13045,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13045 ⟨24,by decide⟩).lower ∧ (cell13045 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13045 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13045 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13045 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13045 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13045 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13045,cell13045,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13045 ⟨25,by decide⟩).lower ∧ (cell13045 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13045 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13045 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13045 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13045 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13045 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13045,cell13045,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13045 ⟨26,by decide⟩).lower ∧ (cell13045 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13045 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13045 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13045 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13045 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13045 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13045,cell13045,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13045 ⟨27,by decide⟩).lower ∧ (cell13045 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13045 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13045 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13045 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13045 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13045 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13045,cell13045,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13045 ⟨28,by decide⟩).lower ∧ (cell13045 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13045 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13045 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13045 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13045 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13045 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13045,cell13045,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13045 ⟨29,by decide⟩).lower ∧ (cell13045 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13045 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13045 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13045 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13045 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13045 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13045,cell13045,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13045 ⟨30,by decide⟩).lower ∧ (cell13045 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13045 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13045 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13045 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13045 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13045 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13045,cell13045,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13045 ⟨31,by decide⟩).lower ∧ (cell13045 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13045 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13045 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13045 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13045 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13045 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13045,cell13045,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13045 ⟨32,by decide⟩).lower ∧ (cell13045 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13045 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13045 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13045 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13045 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13045 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13045,cell13045,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13045 ⟨33,by decide⟩).lower ∧ (cell13045 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13045 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13045 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13045 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13045 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13045 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13045,cell13045,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13045 ⟨34,by decide⟩).lower ∧ (cell13045 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13045 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13045 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13045 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13045 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13045 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13045,cell13045,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13045 ⟨35,by decide⟩).lower ∧ (cell13045 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13045 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13045 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13045 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13045 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13045 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13045,cell13045,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13045 ⟨36,by decide⟩).lower ∧ (cell13045 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13045 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13045 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13045 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13045 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13045 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13045,cell13045,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13045 ⟨37,by decide⟩).lower ∧ (cell13045 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13045 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13045 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13045 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13045 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13045 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13045,cell13045,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13045 ⟨38,by decide⟩).lower ∧ (cell13045 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13045 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13045 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13045 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13045 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13045 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13045,cell13045,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13045 ⟨39,by decide⟩).lower ∧ (cell13045 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13045 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13045 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13045 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13045 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13045 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13045,cell13045,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13045 ⟨40,by decide⟩).lower ∧ (cell13045 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13045 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13045 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13045 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13045 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13045 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13045,cell13045,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13045 ⟨41,by decide⟩).lower ∧ (cell13045 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13045 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13045 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13045 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13045 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13045 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13045,cell13045,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13045 ⟨42,by decide⟩).lower ∧ (cell13045 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13045 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13045 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13045 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13045 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13045 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13045,cell13045,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13045 ⟨43,by decide⟩).lower ∧ (cell13045 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13045 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13045 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13045 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13045 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13045 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13045,cell13045,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13045 ⟨44,by decide⟩).lower ∧ (cell13045 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13045 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13045 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13045 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13045 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13045 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13045,cell13045,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13045 ⟨45,by decide⟩).lower ∧ (cell13045 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13045 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13045 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13045 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13045 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13045 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13045,cell13045,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13045 ⟨46,by decide⟩).lower ∧ (cell13045 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13045 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13045 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13045 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13045 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13045 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13045,cell13045,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13045 ⟨47,by decide⟩).lower ∧ (cell13045 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13045 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13045 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13045 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13045 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13045 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13045,cell13045,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13045 ⟨48,by decide⟩).lower ∧ (cell13045 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13045 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13045 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13045 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13045 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13045 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13045,cell13045,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13045 ⟨49,by decide⟩).lower ∧ (cell13045 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13045 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13045 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13045 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13045 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13045 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13045,cell13045,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13045 ⟨50,by decide⟩).lower ∧ (cell13045 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13045 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13045 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13045 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13045 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13045 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13045,cell13045,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13045 ⟨51,by decide⟩).lower ∧ (cell13045 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13045 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13045 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13045 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13045 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13045 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13045,cell13045,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13045 ⟨52,by decide⟩).lower ∧ (cell13045 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13045 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13045 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13045 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13045 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13045 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13045,cell13045,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13045 i).lower ∧
    (cell13045 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13045 i).upper ≤ (0.532 : ℝ) ∧
    (cell13045 i).centre ≤ (0.1 : ℝ) ∧ (cell13045 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13045 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13045 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13045

/-! The local source numeric instances at 13045 have no network premises. -/
namespace BstLean.Part269.N13045
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13045)
open BstLean.Part268 (cell13045)

noncomputable def sourceNumerics13045 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13045 (cell13045 i)
      scalarRow13045.M scalarRow13045.H scalarRow13045.xi := by
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
    energy_allowance := scalarRow13045.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13045]
    centre_nonneg := (scalarRow13045.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D27.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13045])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13045
/-! Actual 13046 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13046
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13046 ≤ (1.035327023677 : ℝ) := by
  have hr : (114.219087721798 : ℝ) ≤ √(13046 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.219087721798 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13046 13046 (11 / 1000) ≤
    (0.008368889568 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13046) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.219087721798 : ℝ) ≤ √(13046 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13046)
  have hdiv : K / √(13046 : ℝ) ≤ K / 114.219087721798 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.219087721798 ≤ (0.008368889568 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13046.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13046 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13046 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13046 := gPlus_lower 13046
end BstLean.Part269.N13046

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13046
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035327023676 : ℝ) ≤ wn 13046 := by
  have hn : √(13046 : ℝ) ≤ 114.219087721799 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13046 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.219087721799 ≤ 2 / √(13046 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000245086453 : ℝ) ≤ rhoBar 13046 BstLean.Part154.csC ∧
    rhoBar 13046 BstLean.Part154.csC ≤ 0.000245086833 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035327023676 : ℝ) / (1.295212 * 13046) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035327023677 : ℝ) / (1.29521 * 13046) := by gcongr
      _ ≤ (0.000245086833 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13046 BstLean.Part154.csC) ≤ 0.000980407400 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13046 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13046 BstLean.Part154.csC) (piBar (rhoBar 13046 BstLean.Part154.csC)) ≤ 0.000187198742 ∧
    cc1 (rhoBar 13046 BstLean.Part154.csC) (piBar (rhoBar 13046 BstLean.Part154.csC)) ≤ 0.000119115850 ∧
    cc2 (rhoBar 13046 BstLean.Part154.csC) ≤ 0.000069147723 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13046 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13046 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13046 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13046 BstLean.Part154.csC * nuR (rhoBar 13046 BstLean.Part154.csC)) ≤ 0.000490188683 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000245086833 : ℝ) * 0.000980407400 := by gcongr
      _ ≤ (0.000490188683 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13046 BstLean.Part154.csC) * nuR (rhoBar 13046 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000980407400 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13046 BstLean.Part154.csC) * rhoBar 13046 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000245086833 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000245086833 / 2 + 0.399 * 0.000980407400 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000187198742 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000490188683 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119115850 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000245086833 / 1.414213562 := by gcongr
      _ ≤ (0.000069147723 : ℝ) := by norm_num

end BstLean.Part269.N13046

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13046
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13046 BstLean.Part154.csC) (piBar (rhoBar 13046 BstLean.Part154.csC)) ≤ 1.51336E-7 := by
  have hr0 : 0 ≤ rhoBar 13046 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13046 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13046 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13046 BstLean.Part154.csC) (piBar (rhoBar 13046 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13046 BstLean.Part154.csC) (piBar (rhoBar 13046 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13046 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000187198742 : ℝ) ^ 2 + 0.000119115850 ^ 2 + 3 * 0.000069147723 ^ 2 +
        2 * 0.797885 * 0.000187198742 * 0.000119115850 + 2 * 0.000187198742 * 0.000069147723 +
        4 * 0.797885 * 0.000119115850 * 0.000069147723 := by gcongr
    _ ≤ (1.51336E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13046 BstLean.Part154.csC Θ ≤ 0.002557175210 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13046 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13046 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13046 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13046 BstLean.Part154.csC) (piBar (rhoBar 13046 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13046 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035327023677 * 1.51336E-7 / (0.000245086453 : ℝ) := by gcongr
    _ ≤ 0.002557175210 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13046 BstLean.Part154.csC Θ ≤ 0.002835996513 + 0.000646156526 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13046 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13046 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13046 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035327023677 : ℝ) * ((2 * Θ * 0.000245086833 +
        (6863 / 10000) * 0.000245086833 * 13046 * 0.000980407400) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002835996513 + 0.000646156526 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13046 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13046 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13046 0.011 Θ ∧ gammaRatio 13046 0.011 Θ ≤ 0.000084254516 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13046 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035327023677 : ℝ) * 0.525 / ((1 - 0.011) * 13046) := by gcongr
      _ ≤ (0.000084254516 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13046 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13046 0.011 Θ) :=
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
    badAllowance 13046 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000383431726 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13046 BstLean.Part154.csC) 1.22 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 2 (rhoBar 13046 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13046 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13046 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13046 0.011 Θ) 1.12 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 1 (gammaRatio 13046 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13046 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13046 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13046 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13046 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035327023677 : ℝ) * 13046 *
        (1.3781E-8 / 1.1045361 + 1.6832E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000383431726 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13046 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003219428239 + 0.003203331736 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13046

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13046
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13046 BstLean.Part154.csC) (piBar (rhoBar 13046 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13046 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13046 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13046 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13046 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13046 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13046 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13046 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13046 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13046 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13046 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13046 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13046 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13046 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13046 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051776157412 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13046) ≤ 0.010455674309 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13046 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035327023677)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010455674309 + 2 * 0.737676 / 13046) := by gcongr
    _ ≤ (0.051776157412 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13046 12 ≤ 0.0015 := by
  exact BstLean.Part269.S27.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13046

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13046
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560518800452 : ℝ) ≤ plow 13046 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13046) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052407777401)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001342516986) : eMP 13046 0.011 xi bn ≤ 0.001156239165 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13046 : ℝ) * (1 - 0.011))) ≤ 0.000571739269 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001342516986 / (13046 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000571739269 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000571739269 : ℝ) + 3.141593 * 0.052407777401 / (13046 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001156239165 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052407777401)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001342516986) : PiBarMP 13046 12 0.011 xi bn ≤ 0.159077152145 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13046 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036640373716 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.589145608196 : ℝ) ≤ √((13046 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.219087721798 : ℝ) ≤ √(13046 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13046) ≤ 0.121979684313 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036640373716 + 0.052407777401 * 1.772454 / (2 * (113.589145608196 : ℝ))) * (1 + 0.001156239165) +
        8 / (13046 * 114.219087721798) + 0.121979684313 := by gcongr
    _ ≤ (0.159077152145 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052407777401)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001342516986) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280703607494) :
    parallelOracle 13046 0.011 xi bn cd ≤ 0.160041259404 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13046 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13046 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560518800452 : ℝ) ≤ plow 13046 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.219087721798 : ℝ) ≤ √(13046 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280703607494 : ℝ) / (2 * 0.560518800452 * 114.219087721798)) * 0.159077152145 +
        0.280703607494 ^ 2 / (2 * 0.560518800452 * 114.219087721798) := by gcongr
    _ ≤ (0.160041259404 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052407777401) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001342516986)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280703607494) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13046 13046 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560518800452 : ℝ) ≤ plow 13046 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.219087721798 : ℝ) ≤ √(13046 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13046 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13046 Θ 1.22 ≤ 0.011610147888 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.219087721798 := by gcongr <;> linarith
      _ ≤ (0.011610147888 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13046 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13046 13046 0.011 ≤ 0.008368889568 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13046 13046 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13046 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13046 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13046 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13046 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160041259404 + 0.011610147888 + (0.008368889568 : ℝ) *
        (1 + 2 * (0.280703607494 + 0.011610147888) / (0.560518800452 * 114.219087721798))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13046]

end BstLean.Part269.N13046

/-! The original eight local profiles supply actual 13046 moment certificates. -/
namespace BstLean.Part269.N13046
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13046 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13046 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13046 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052407777401 ∧
    0 ≤ bN 13046 BstLean.Part154.csC (groupTheta g) ∧ bN 13046 BstLean.Part154.csC (groupTheta g) ≤ 0.001342516986 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13046 13046 0.011
      (momentAllowance 13046 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13046 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13046 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13046 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13046 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13046 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228927450082 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13046 0.011
      (momentAllowance 13046 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13046 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13046
/-! The actual computed-centre upper energy formula at 13046. -/
namespace BstLean.Part269.N13046
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13046

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13046
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13046)
open BstLean.Part268 (cell13046)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084540501037
  | 2 => 0.085467614121
  | 3 => 0.086390701425
  | 4 => 0.087310672142
  | 5 => 0.088228640801
  | 6 => 0.089145959583
  | 7 => 0.090064254039
  | 8 => 0.090985462299
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13046 13046 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13046 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N13046

/-! Actual upper energy certificates on all 43 source endpoints at 13046. -/
namespace BstLean.Part269.N13046
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13046)
open BstLean.Part268 (cell13046)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13046 (gMinus 13046) (1 - (cell13046 i).lower) ≤ 1 ∧
    energyUpper 13046 (gMinus 13046) (BstLean.Part211.gPlus 13046)
      (finiteEnergy 13046 13046 0.011) (1 - (cell13046 i).lower) ≤
      (cell13046 i).energy := by
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
      have E := BstLean.Part269.S27.uniformEnergy10 (n := 13046) (by norm_num)
        (q := 1 - (cell13046 ⟨10,by decide⟩).lower)
        (by norm_num [cell13046]) (by norm_num [cell13046])
      exact ⟨E.1,E.2.trans (by norm_num [cell13046])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy11 (n := 13046) (by norm_num)
        (q := 1 - (cell13046 ⟨11,by decide⟩).lower)
        (by norm_num [cell13046]) (by norm_num [cell13046])
      exact ⟨E.1,E.2.trans (by norm_num [cell13046])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy12 (n := 13046) (by norm_num)
        (q := 1 - (cell13046 ⟨12,by decide⟩).lower)
        (by norm_num [cell13046]) (by norm_num [cell13046])
      exact ⟨E.1,E.2.trans (by norm_num [cell13046])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy13 (n := 13046) (by norm_num)
        (q := 1 - (cell13046 ⟨13,by decide⟩).lower)
        (by norm_num [cell13046]) (by norm_num [cell13046])
      exact ⟨E.1,E.2.trans (by norm_num [cell13046])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy14 (n := 13046) (by norm_num)
        (q := 1 - (cell13046 ⟨14,by decide⟩).lower)
        (by norm_num [cell13046]) (by norm_num [cell13046])
      exact ⟨E.1,E.2.trans (by norm_num [cell13046])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy15 (n := 13046) (by norm_num)
        (q := 1 - (cell13046 ⟨15,by decide⟩).lower)
        (by norm_num [cell13046]) (by norm_num [cell13046])
      exact ⟨E.1,E.2.trans (by norm_num [cell13046])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy16 (n := 13046) (by norm_num)
        (q := 1 - (cell13046 ⟨16,by decide⟩).lower)
        (by norm_num [cell13046]) (by norm_num [cell13046])
      exact ⟨E.1,E.2.trans (by norm_num [cell13046])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy17 (n := 13046) (by norm_num)
        (q := 1 - (cell13046 ⟨17,by decide⟩).lower)
        (by norm_num [cell13046]) (by norm_num [cell13046])
      exact ⟨E.1,E.2.trans (by norm_num [cell13046])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy18 (n := 13046) (by norm_num)
        (q := 1 - (cell13046 ⟨18,by decide⟩).lower)
        (by norm_num [cell13046]) (by norm_num [cell13046])
      exact ⟨E.1,E.2.trans (by norm_num [cell13046])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy19 (n := 13046) (by norm_num)
        (q := 1 - (cell13046 ⟨19,by decide⟩).lower)
        (by norm_num [cell13046]) (by norm_num [cell13046])
      exact ⟨E.1,E.2.trans (by norm_num [cell13046])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy20 (n := 13046) (by norm_num)
        (q := 1 - (cell13046 ⟨20,by decide⟩).lower)
        (by norm_num [cell13046]) (by norm_num [cell13046])
      exact ⟨E.1,E.2.trans (by norm_num [cell13046])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy21 (n := 13046) (by norm_num)
        (q := 1 - (cell13046 ⟨21,by decide⟩).lower)
        (by norm_num [cell13046]) (by norm_num [cell13046])
      exact ⟨E.1,E.2.trans (by norm_num [cell13046])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy22 (n := 13046) (by norm_num)
        (q := 1 - (cell13046 ⟨22,by decide⟩).lower)
        (by norm_num [cell13046]) (by norm_num [cell13046])
      exact ⟨E.1,E.2.trans (by norm_num [cell13046])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy23 (n := 13046) (by norm_num)
        (q := 1 - (cell13046 ⟨23,by decide⟩).lower)
        (by norm_num [cell13046]) (by norm_num [cell13046])
      exact ⟨E.1,E.2.trans (by norm_num [cell13046])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy24 (n := 13046) (by norm_num)
        (q := 1 - (cell13046 ⟨24,by decide⟩).lower)
        (by norm_num [cell13046]) (by norm_num [cell13046])
      exact ⟨E.1,E.2.trans (by norm_num [cell13046])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy25 (n := 13046) (by norm_num)
        (q := 1 - (cell13046 ⟨25,by decide⟩).lower)
        (by norm_num [cell13046]) (by norm_num [cell13046])
      exact ⟨E.1,E.2.trans (by norm_num [cell13046])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy26 (n := 13046) (by norm_num)
        (q := 1 - (cell13046 ⟨26,by decide⟩).lower)
        (by norm_num [cell13046]) (by norm_num [cell13046])
      exact ⟨E.1,E.2.trans (by norm_num [cell13046])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy27 (n := 13046) (by norm_num)
        (q := 1 - (cell13046 ⟨27,by decide⟩).lower)
        (by norm_num [cell13046]) (by norm_num [cell13046])
      exact ⟨E.1,E.2.trans (by norm_num [cell13046])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy28 (n := 13046) (by norm_num)
        (q := 1 - (cell13046 ⟨28,by decide⟩).lower)
        (by norm_num [cell13046]) (by norm_num [cell13046])
      exact ⟨E.1,E.2.trans (by norm_num [cell13046])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy29 (n := 13046) (by norm_num)
        (q := 1 - (cell13046 ⟨29,by decide⟩).lower)
        (by norm_num [cell13046]) (by norm_num [cell13046])
      exact ⟨E.1,E.2.trans (by norm_num [cell13046])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy30 (n := 13046) (by norm_num)
        (q := 1 - (cell13046 ⟨30,by decide⟩).lower)
        (by norm_num [cell13046]) (by norm_num [cell13046])
      exact ⟨E.1,E.2.trans (by norm_num [cell13046])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy31 (n := 13046) (by norm_num)
        (q := 1 - (cell13046 ⟨31,by decide⟩).lower)
        (by norm_num [cell13046]) (by norm_num [cell13046])
      exact ⟨E.1,E.2.trans (by norm_num [cell13046])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy32 (n := 13046) (by norm_num)
        (q := 1 - (cell13046 ⟨32,by decide⟩).lower)
        (by norm_num [cell13046]) (by norm_num [cell13046])
      exact ⟨E.1,E.2.trans (by norm_num [cell13046])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy33 (n := 13046) (by norm_num)
        (q := 1 - (cell13046 ⟨33,by decide⟩).lower)
        (by norm_num [cell13046]) (by norm_num [cell13046])
      exact ⟨E.1,E.2.trans (by norm_num [cell13046])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy34 (n := 13046) (by norm_num)
        (q := 1 - (cell13046 ⟨34,by decide⟩).lower)
        (by norm_num [cell13046]) (by norm_num [cell13046])
      exact ⟨E.1,E.2.trans (by norm_num [cell13046])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy35 (n := 13046) (by norm_num)
        (q := 1 - (cell13046 ⟨35,by decide⟩).lower)
        (by norm_num [cell13046]) (by norm_num [cell13046])
      exact ⟨E.1,E.2.trans (by norm_num [cell13046])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy36 (n := 13046) (by norm_num)
        (q := 1 - (cell13046 ⟨36,by decide⟩).lower)
        (by norm_num [cell13046]) (by norm_num [cell13046])
      exact ⟨E.1,E.2.trans (by norm_num [cell13046])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy37 (n := 13046) (by norm_num)
        (q := 1 - (cell13046 ⟨37,by decide⟩).lower)
        (by norm_num [cell13046]) (by norm_num [cell13046])
      exact ⟨E.1,E.2.trans (by norm_num [cell13046])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy38 (n := 13046) (by norm_num)
        (q := 1 - (cell13046 ⟨38,by decide⟩).lower)
        (by norm_num [cell13046]) (by norm_num [cell13046])
      exact ⟨E.1,E.2.trans (by norm_num [cell13046])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy39 (n := 13046) (by norm_num)
        (q := 1 - (cell13046 ⟨39,by decide⟩).lower)
        (by norm_num [cell13046]) (by norm_num [cell13046])
      exact ⟨E.1,E.2.trans (by norm_num [cell13046])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy40 (n := 13046) (by norm_num)
        (q := 1 - (cell13046 ⟨40,by decide⟩).lower)
        (by norm_num [cell13046]) (by norm_num [cell13046])
      exact ⟨E.1,E.2.trans (by norm_num [cell13046])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy41 (n := 13046) (by norm_num)
        (q := 1 - (cell13046 ⟨41,by decide⟩).lower)
        (by norm_num [cell13046]) (by norm_num [cell13046])
      exact ⟨E.1,E.2.trans (by norm_num [cell13046])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy42 (n := 13046) (by norm_num)
        (q := 1 - (cell13046 ⟨42,by decide⟩).lower)
        (by norm_num [cell13046]) (by norm_num [cell13046])
      exact ⟨E.1,E.2.trans (by norm_num [cell13046])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy43 (n := 13046) (by norm_num)
        (q := 1 - (cell13046 ⟨43,by decide⟩).lower)
        (by norm_num [cell13046]) (by norm_num [cell13046])
      exact ⟨E.1,E.2.trans (by norm_num [cell13046])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy44 (n := 13046) (by norm_num)
        (q := 1 - (cell13046 ⟨44,by decide⟩).lower)
        (by norm_num [cell13046]) (by norm_num [cell13046])
      exact ⟨E.1,E.2.trans (by norm_num [cell13046])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy45 (n := 13046) (by norm_num)
        (q := 1 - (cell13046 ⟨45,by decide⟩).lower)
        (by norm_num [cell13046]) (by norm_num [cell13046])
      exact ⟨E.1,E.2.trans (by norm_num [cell13046])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy46 (n := 13046) (by norm_num)
        (q := 1 - (cell13046 ⟨46,by decide⟩).lower)
        (by norm_num [cell13046]) (by norm_num [cell13046])
      exact ⟨E.1,E.2.trans (by norm_num [cell13046])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy47 (n := 13046) (by norm_num)
        (q := 1 - (cell13046 ⟨47,by decide⟩).lower)
        (by norm_num [cell13046]) (by norm_num [cell13046])
      exact ⟨E.1,E.2.trans (by norm_num [cell13046])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy48 (n := 13046) (by norm_num)
        (q := 1 - (cell13046 ⟨48,by decide⟩).lower)
        (by norm_num [cell13046]) (by norm_num [cell13046])
      exact ⟨E.1,E.2.trans (by norm_num [cell13046])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy49 (n := 13046) (by norm_num)
        (q := 1 - (cell13046 ⟨49,by decide⟩).lower)
        (by norm_num [cell13046]) (by norm_num [cell13046])
      exact ⟨E.1,E.2.trans (by norm_num [cell13046])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy50 (n := 13046) (by norm_num)
        (q := 1 - (cell13046 ⟨50,by decide⟩).lower)
        (by norm_num [cell13046]) (by norm_num [cell13046])
      exact ⟨E.1,E.2.trans (by norm_num [cell13046])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy51 (n := 13046) (by norm_num)
        (q := 1 - (cell13046 ⟨51,by decide⟩).lower)
        (by norm_num [cell13046]) (by norm_num [cell13046])
      exact ⟨E.1,E.2.trans (by norm_num [cell13046])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy52 (n := 13046) (by norm_num)
        (q := 1 - (cell13046 ⟨52,by decide⟩).lower)
        (by norm_num [cell13046]) (by norm_num [cell13046])
      exact ⟨E.1,E.2.trans (by norm_num [cell13046])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13046

/-! Source-cell containment and simple scalar guards at 13046. -/
namespace BstLean.Part269.N13046
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13046)
open BstLean.Part268 (cell13046)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13046 ⟨10,by decide⟩).lower ∧ (cell13046 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13046 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13046 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13046 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13046 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13046 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13046,cell13046,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13046 ⟨11,by decide⟩).lower ∧ (cell13046 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13046 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13046 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13046 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13046 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13046 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13046,cell13046,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13046 ⟨12,by decide⟩).lower ∧ (cell13046 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13046 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13046 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13046 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13046 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13046 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13046,cell13046,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13046 ⟨13,by decide⟩).lower ∧ (cell13046 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13046 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13046 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13046 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13046 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13046 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13046,cell13046,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13046 ⟨14,by decide⟩).lower ∧ (cell13046 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13046 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13046 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13046 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13046 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13046 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13046,cell13046,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13046 ⟨15,by decide⟩).lower ∧ (cell13046 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13046 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13046 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13046 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13046 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13046 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13046,cell13046,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13046 ⟨16,by decide⟩).lower ∧ (cell13046 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13046 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13046 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13046 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13046 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13046 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13046,cell13046,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13046 ⟨17,by decide⟩).lower ∧ (cell13046 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13046 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13046 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13046 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13046 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13046 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13046,cell13046,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13046 ⟨18,by decide⟩).lower ∧ (cell13046 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13046 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13046 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13046 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13046 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13046 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13046,cell13046,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13046 ⟨19,by decide⟩).lower ∧ (cell13046 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13046 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13046 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13046 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13046 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13046 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13046,cell13046,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13046 ⟨20,by decide⟩).lower ∧ (cell13046 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13046 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13046 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13046 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13046 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13046 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13046,cell13046,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13046 ⟨21,by decide⟩).lower ∧ (cell13046 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13046 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13046 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13046 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13046 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13046 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13046,cell13046,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13046 ⟨22,by decide⟩).lower ∧ (cell13046 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13046 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13046 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13046 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13046 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13046 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13046,cell13046,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13046 ⟨23,by decide⟩).lower ∧ (cell13046 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13046 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13046 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13046 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13046 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13046 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13046,cell13046,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13046 ⟨24,by decide⟩).lower ∧ (cell13046 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13046 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13046 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13046 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13046 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13046 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13046,cell13046,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13046 ⟨25,by decide⟩).lower ∧ (cell13046 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13046 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13046 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13046 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13046 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13046 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13046,cell13046,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13046 ⟨26,by decide⟩).lower ∧ (cell13046 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13046 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13046 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13046 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13046 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13046 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13046,cell13046,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13046 ⟨27,by decide⟩).lower ∧ (cell13046 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13046 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13046 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13046 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13046 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13046 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13046,cell13046,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13046 ⟨28,by decide⟩).lower ∧ (cell13046 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13046 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13046 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13046 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13046 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13046 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13046,cell13046,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13046 ⟨29,by decide⟩).lower ∧ (cell13046 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13046 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13046 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13046 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13046 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13046 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13046,cell13046,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13046 ⟨30,by decide⟩).lower ∧ (cell13046 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13046 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13046 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13046 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13046 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13046 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13046,cell13046,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13046 ⟨31,by decide⟩).lower ∧ (cell13046 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13046 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13046 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13046 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13046 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13046 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13046,cell13046,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13046 ⟨32,by decide⟩).lower ∧ (cell13046 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13046 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13046 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13046 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13046 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13046 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13046,cell13046,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13046 ⟨33,by decide⟩).lower ∧ (cell13046 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13046 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13046 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13046 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13046 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13046 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13046,cell13046,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13046 ⟨34,by decide⟩).lower ∧ (cell13046 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13046 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13046 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13046 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13046 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13046 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13046,cell13046,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13046 ⟨35,by decide⟩).lower ∧ (cell13046 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13046 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13046 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13046 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13046 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13046 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13046,cell13046,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13046 ⟨36,by decide⟩).lower ∧ (cell13046 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13046 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13046 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13046 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13046 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13046 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13046,cell13046,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13046 ⟨37,by decide⟩).lower ∧ (cell13046 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13046 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13046 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13046 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13046 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13046 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13046,cell13046,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13046 ⟨38,by decide⟩).lower ∧ (cell13046 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13046 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13046 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13046 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13046 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13046 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13046,cell13046,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13046 ⟨39,by decide⟩).lower ∧ (cell13046 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13046 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13046 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13046 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13046 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13046 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13046,cell13046,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13046 ⟨40,by decide⟩).lower ∧ (cell13046 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13046 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13046 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13046 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13046 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13046 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13046,cell13046,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13046 ⟨41,by decide⟩).lower ∧ (cell13046 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13046 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13046 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13046 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13046 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13046 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13046,cell13046,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13046 ⟨42,by decide⟩).lower ∧ (cell13046 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13046 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13046 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13046 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13046 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13046 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13046,cell13046,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13046 ⟨43,by decide⟩).lower ∧ (cell13046 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13046 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13046 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13046 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13046 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13046 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13046,cell13046,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13046 ⟨44,by decide⟩).lower ∧ (cell13046 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13046 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13046 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13046 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13046 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13046 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13046,cell13046,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13046 ⟨45,by decide⟩).lower ∧ (cell13046 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13046 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13046 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13046 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13046 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13046 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13046,cell13046,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13046 ⟨46,by decide⟩).lower ∧ (cell13046 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13046 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13046 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13046 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13046 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13046 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13046,cell13046,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13046 ⟨47,by decide⟩).lower ∧ (cell13046 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13046 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13046 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13046 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13046 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13046 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13046,cell13046,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13046 ⟨48,by decide⟩).lower ∧ (cell13046 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13046 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13046 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13046 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13046 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13046 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13046,cell13046,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13046 ⟨49,by decide⟩).lower ∧ (cell13046 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13046 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13046 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13046 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13046 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13046 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13046,cell13046,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13046 ⟨50,by decide⟩).lower ∧ (cell13046 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13046 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13046 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13046 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13046 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13046 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13046,cell13046,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13046 ⟨51,by decide⟩).lower ∧ (cell13046 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13046 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13046 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13046 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13046 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13046 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13046,cell13046,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13046 ⟨52,by decide⟩).lower ∧ (cell13046 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13046 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13046 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13046 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13046 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13046 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13046,cell13046,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13046 i).lower ∧
    (cell13046 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13046 i).upper ≤ (0.532 : ℝ) ∧
    (cell13046 i).centre ≤ (0.1 : ℝ) ∧ (cell13046 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13046 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13046 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13046

/-! The local source numeric instances at 13046 have no network premises. -/
namespace BstLean.Part269.N13046
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13046)
open BstLean.Part268 (cell13046)

noncomputable def sourceNumerics13046 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13046 (cell13046 i)
      scalarRow13046.M scalarRow13046.H scalarRow13046.xi := by
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
    energy_allowance := scalarRow13046.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13046]
    centre_nonneg := (scalarRow13046.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D27.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13046])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13046
/-! Actual 13047 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13047
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13047 ≤ (1.035325658064 : ℝ) := by
  have hr : (114.223465189951 : ℝ) ≤ √(13047 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.223465189951 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13047 13047 (11 / 1000) ≤
    (0.008368568838 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13047) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.223465189951 : ℝ) ≤ √(13047 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13047)
  have hdiv : K / √(13047 : ℝ) ≤ K / 114.223465189951 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.223465189951 ≤ (0.008368568838 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13047.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13047 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13047 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13047 := gPlus_lower 13047
end BstLean.Part269.N13047

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13047
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035325658063 : ℝ) ≤ wn 13047 := by
  have hn : √(13047 : ℝ) ≤ 114.223465189952 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13047 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.223465189952 ≤ 2 / √(13047 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000245067345 : ℝ) ≤ rhoBar 13047 BstLean.Part154.csC ∧
    rhoBar 13047 BstLean.Part154.csC ≤ 0.000245067724 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035325658063 : ℝ) / (1.295212 * 13047) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035325658064 : ℝ) / (1.29521 * 13047) := by gcongr
      _ ≤ (0.000245067724 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13047 BstLean.Part154.csC) ≤ 0.000980330955 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13047 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13047 BstLean.Part154.csC) (piBar (rhoBar 13047 BstLean.Part154.csC)) ≤ 0.000187184145 ∧
    cc1 (rhoBar 13047 BstLean.Part154.csC) (piBar (rhoBar 13047 BstLean.Part154.csC)) ≤ 0.000119106563 ∧
    cc2 (rhoBar 13047 BstLean.Part154.csC) ≤ 0.000069142331 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13047 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13047 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13047 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13047 BstLean.Part154.csC * nuR (rhoBar 13047 BstLean.Part154.csC)) ≤ 0.000490150463 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000245067724 : ℝ) * 0.000980330955 := by gcongr
      _ ≤ (0.000490150463 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13047 BstLean.Part154.csC) * nuR (rhoBar 13047 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000980330955 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13047 BstLean.Part154.csC) * rhoBar 13047 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000245067724 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000245067724 / 2 + 0.399 * 0.000980330955 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000187184145 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000490150463 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119106563 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000245067724 / 1.414213562 := by gcongr
      _ ≤ (0.000069142331 : ℝ) := by norm_num

end BstLean.Part269.N13047

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13047
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13047 BstLean.Part154.csC) (piBar (rhoBar 13047 BstLean.Part154.csC)) ≤ 1.51312E-7 := by
  have hr0 : 0 ≤ rhoBar 13047 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13047 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13047 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13047 BstLean.Part154.csC) (piBar (rhoBar 13047 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13047 BstLean.Part154.csC) (piBar (rhoBar 13047 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13047 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000187184145 : ℝ) ^ 2 + 0.000119106563 ^ 2 + 3 * 0.000069142331 ^ 2 +
        2 * 0.797885 * 0.000187184145 * 0.000119106563 + 2 * 0.000187184145 * 0.000069142331 +
        4 * 0.797885 * 0.000119106563 * 0.000069142331 := by gcongr
    _ ≤ (1.51312E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13047 BstLean.Part154.csC Θ ≤ 0.002556965654 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13047 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13047 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13047 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13047 BstLean.Part154.csC) (piBar (rhoBar 13047 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13047 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035325658064 * 1.51312E-7 / (0.000245067345 : ℝ) := by gcongr
    _ ≤ 0.002556965654 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13047 BstLean.Part154.csC Θ ≤ 0.002835767893 + 0.000646105294 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13047 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13047 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13047 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035325658064 : ℝ) * ((2 * Θ * 0.000245067724 +
        (6863 / 10000) * 0.000245067724 * 13047 * 0.000980330955) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002835767893 + 0.000646105294 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13047 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13047 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13047 0.011 Θ ∧ gammaRatio 13047 0.011 Θ ≤ 0.000084247947 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13047 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035325658064 : ℝ) * 0.525 / ((1 - 0.011) * 13047) := by gcongr
      _ ≤ (0.000084247947 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13047 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13047 0.011 Θ) :=
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
    badAllowance 13047 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000383431726 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13047 BstLean.Part154.csC) 1.22 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 2 (rhoBar 13047 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13047 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13047 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13047 0.011 Θ) 1.12 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 1 (gammaRatio 13047 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13047 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13047 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13047 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13047 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035325658064 : ℝ) * 13047 *
        (1.3781E-8 / 1.1045361 + 1.6832E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000383431726 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13047 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003219199619 + 0.003203070948 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13047

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13047
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13047 BstLean.Part154.csC) (piBar (rhoBar 13047 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13047 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13047 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13047 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13047 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13047 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13047 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13047 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13047 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13047 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13047 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13047 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13047 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13047 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13047 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051774151928 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13047) ≤ 0.010455273609 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13047 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035325658064)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010455273609 + 2 * 0.737676 / 13047) := by gcongr
    _ ≤ (0.051774151928 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13047 12 ≤ 0.0015 := by
  exact BstLean.Part269.S27.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13047

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13047
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560518843304 : ℝ) ≤ plow 13047 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13047) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052407411867)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001342406969) : eMP 13047 0.011 xi bn ≤ 0.001156147424 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13047 : ℝ) * (1 - 0.011))) ≤ 0.000571693932 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001342406969 / (13047 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000571693932 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000571693932 : ℝ) + 3.141593 * 0.052407411867 / (13047 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001156147424 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052407411867)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001342406969) : PiBarMP 13047 12 0.011 xi bn ≤ 0.159070951795 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13047 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036638872377 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.593498933697 : ℝ) ≤ √((13047 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.223465189951 : ℝ) ≤ √(13047 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13047) ≤ 0.121975009598 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036638872377 + 0.052407411867 * 1.772454 / (2 * (113.593498933697 : ℝ))) * (1 + 0.001156147424) +
        8 / (13047 * 114.223465189951) + 0.121975009598 := by gcongr
    _ ≤ (0.159070951795 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052407411867)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001342406969) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280700803647) :
    parallelOracle 13047 0.011 xi bn cd ≤ 0.160034992664 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13047 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13047 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560518843304 : ℝ) ≤ plow 13047 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.223465189951 : ℝ) ≤ √(13047 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280700803647 : ℝ) / (2 * 0.560518843304 * 114.223465189951)) * 0.159070951795 +
        0.280700803647 ^ 2 / (2 * 0.560518843304 * 114.223465189951) := by gcongr
    _ ≤ (0.160034992664 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052407411867) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001342406969)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280700803647) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13047 13047 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560518843304 : ℝ) ≤ plow 13047 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.223465189951 : ℝ) ≤ √(13047 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13047 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13047 Θ 1.22 ≤ 0.011609702944 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.223465189951 := by gcongr <;> linarith
      _ ≤ (0.011609702944 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13047 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13047 13047 0.011 ≤ 0.008368568838 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13047 13047 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13047 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13047 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13047 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13047 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160034992664 + 0.011609702944 + (0.008368568838 : ℝ) *
        (1 + 2 * (0.280700803647 + 0.011609702944) / (0.560518843304 * 114.223465189951))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13047]

end BstLean.Part269.N13047

/-! The original eight local profiles supply actual 13047 moment certificates. -/
namespace BstLean.Part269.N13047
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13047 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13047 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13047 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052407411867 ∧
    0 ≤ bN 13047 BstLean.Part154.csC (groupTheta g) ∧ bN 13047 BstLean.Part154.csC (groupTheta g) ≤ 0.001342406969 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13047 13047 0.011
      (momentAllowance 13047 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13047 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13047 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13047 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13047 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13047 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228926651719 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13047 0.011
      (momentAllowance 13047 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13047 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13047
/-! The actual computed-centre upper energy formula at 13047. -/
namespace BstLean.Part269.N13047
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13047

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13047
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13047)
open BstLean.Part268 (cell13047)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084537919183
  | 2 => 0.085464998993
  | 3 => 0.086388048073
  | 4 => 0.087307974452
  | 5 => 0.088225891275
  | 6 => 0.089143149101
  | 7 => 0.090061371584
  | 8 => 0.090982494653
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13047 13047 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13047 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N13047

/-! Actual upper energy certificates on all 43 source endpoints at 13047. -/
namespace BstLean.Part269.N13047
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13047)
open BstLean.Part268 (cell13047)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13047 (gMinus 13047) (1 - (cell13047 i).lower) ≤ 1 ∧
    energyUpper 13047 (gMinus 13047) (BstLean.Part211.gPlus 13047)
      (finiteEnergy 13047 13047 0.011) (1 - (cell13047 i).lower) ≤
      (cell13047 i).energy := by
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
      have E := BstLean.Part269.S27.uniformEnergy10 (n := 13047) (by norm_num)
        (q := 1 - (cell13047 ⟨10,by decide⟩).lower)
        (by norm_num [cell13047]) (by norm_num [cell13047])
      exact ⟨E.1,E.2.trans (by norm_num [cell13047])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy11 (n := 13047) (by norm_num)
        (q := 1 - (cell13047 ⟨11,by decide⟩).lower)
        (by norm_num [cell13047]) (by norm_num [cell13047])
      exact ⟨E.1,E.2.trans (by norm_num [cell13047])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy12 (n := 13047) (by norm_num)
        (q := 1 - (cell13047 ⟨12,by decide⟩).lower)
        (by norm_num [cell13047]) (by norm_num [cell13047])
      exact ⟨E.1,E.2.trans (by norm_num [cell13047])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy13 (n := 13047) (by norm_num)
        (q := 1 - (cell13047 ⟨13,by decide⟩).lower)
        (by norm_num [cell13047]) (by norm_num [cell13047])
      exact ⟨E.1,E.2.trans (by norm_num [cell13047])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy14 (n := 13047) (by norm_num)
        (q := 1 - (cell13047 ⟨14,by decide⟩).lower)
        (by norm_num [cell13047]) (by norm_num [cell13047])
      exact ⟨E.1,E.2.trans (by norm_num [cell13047])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy15 (n := 13047) (by norm_num)
        (q := 1 - (cell13047 ⟨15,by decide⟩).lower)
        (by norm_num [cell13047]) (by norm_num [cell13047])
      exact ⟨E.1,E.2.trans (by norm_num [cell13047])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy16 (n := 13047) (by norm_num)
        (q := 1 - (cell13047 ⟨16,by decide⟩).lower)
        (by norm_num [cell13047]) (by norm_num [cell13047])
      exact ⟨E.1,E.2.trans (by norm_num [cell13047])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy17 (n := 13047) (by norm_num)
        (q := 1 - (cell13047 ⟨17,by decide⟩).lower)
        (by norm_num [cell13047]) (by norm_num [cell13047])
      exact ⟨E.1,E.2.trans (by norm_num [cell13047])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy18 (n := 13047) (by norm_num)
        (q := 1 - (cell13047 ⟨18,by decide⟩).lower)
        (by norm_num [cell13047]) (by norm_num [cell13047])
      exact ⟨E.1,E.2.trans (by norm_num [cell13047])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy19 (n := 13047) (by norm_num)
        (q := 1 - (cell13047 ⟨19,by decide⟩).lower)
        (by norm_num [cell13047]) (by norm_num [cell13047])
      exact ⟨E.1,E.2.trans (by norm_num [cell13047])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy20 (n := 13047) (by norm_num)
        (q := 1 - (cell13047 ⟨20,by decide⟩).lower)
        (by norm_num [cell13047]) (by norm_num [cell13047])
      exact ⟨E.1,E.2.trans (by norm_num [cell13047])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy21 (n := 13047) (by norm_num)
        (q := 1 - (cell13047 ⟨21,by decide⟩).lower)
        (by norm_num [cell13047]) (by norm_num [cell13047])
      exact ⟨E.1,E.2.trans (by norm_num [cell13047])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy22 (n := 13047) (by norm_num)
        (q := 1 - (cell13047 ⟨22,by decide⟩).lower)
        (by norm_num [cell13047]) (by norm_num [cell13047])
      exact ⟨E.1,E.2.trans (by norm_num [cell13047])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy23 (n := 13047) (by norm_num)
        (q := 1 - (cell13047 ⟨23,by decide⟩).lower)
        (by norm_num [cell13047]) (by norm_num [cell13047])
      exact ⟨E.1,E.2.trans (by norm_num [cell13047])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy24 (n := 13047) (by norm_num)
        (q := 1 - (cell13047 ⟨24,by decide⟩).lower)
        (by norm_num [cell13047]) (by norm_num [cell13047])
      exact ⟨E.1,E.2.trans (by norm_num [cell13047])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy25 (n := 13047) (by norm_num)
        (q := 1 - (cell13047 ⟨25,by decide⟩).lower)
        (by norm_num [cell13047]) (by norm_num [cell13047])
      exact ⟨E.1,E.2.trans (by norm_num [cell13047])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy26 (n := 13047) (by norm_num)
        (q := 1 - (cell13047 ⟨26,by decide⟩).lower)
        (by norm_num [cell13047]) (by norm_num [cell13047])
      exact ⟨E.1,E.2.trans (by norm_num [cell13047])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy27 (n := 13047) (by norm_num)
        (q := 1 - (cell13047 ⟨27,by decide⟩).lower)
        (by norm_num [cell13047]) (by norm_num [cell13047])
      exact ⟨E.1,E.2.trans (by norm_num [cell13047])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy28 (n := 13047) (by norm_num)
        (q := 1 - (cell13047 ⟨28,by decide⟩).lower)
        (by norm_num [cell13047]) (by norm_num [cell13047])
      exact ⟨E.1,E.2.trans (by norm_num [cell13047])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy29 (n := 13047) (by norm_num)
        (q := 1 - (cell13047 ⟨29,by decide⟩).lower)
        (by norm_num [cell13047]) (by norm_num [cell13047])
      exact ⟨E.1,E.2.trans (by norm_num [cell13047])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy30 (n := 13047) (by norm_num)
        (q := 1 - (cell13047 ⟨30,by decide⟩).lower)
        (by norm_num [cell13047]) (by norm_num [cell13047])
      exact ⟨E.1,E.2.trans (by norm_num [cell13047])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy31 (n := 13047) (by norm_num)
        (q := 1 - (cell13047 ⟨31,by decide⟩).lower)
        (by norm_num [cell13047]) (by norm_num [cell13047])
      exact ⟨E.1,E.2.trans (by norm_num [cell13047])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy32 (n := 13047) (by norm_num)
        (q := 1 - (cell13047 ⟨32,by decide⟩).lower)
        (by norm_num [cell13047]) (by norm_num [cell13047])
      exact ⟨E.1,E.2.trans (by norm_num [cell13047])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy33 (n := 13047) (by norm_num)
        (q := 1 - (cell13047 ⟨33,by decide⟩).lower)
        (by norm_num [cell13047]) (by norm_num [cell13047])
      exact ⟨E.1,E.2.trans (by norm_num [cell13047])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy34 (n := 13047) (by norm_num)
        (q := 1 - (cell13047 ⟨34,by decide⟩).lower)
        (by norm_num [cell13047]) (by norm_num [cell13047])
      exact ⟨E.1,E.2.trans (by norm_num [cell13047])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy35 (n := 13047) (by norm_num)
        (q := 1 - (cell13047 ⟨35,by decide⟩).lower)
        (by norm_num [cell13047]) (by norm_num [cell13047])
      exact ⟨E.1,E.2.trans (by norm_num [cell13047])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy36 (n := 13047) (by norm_num)
        (q := 1 - (cell13047 ⟨36,by decide⟩).lower)
        (by norm_num [cell13047]) (by norm_num [cell13047])
      exact ⟨E.1,E.2.trans (by norm_num [cell13047])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy37 (n := 13047) (by norm_num)
        (q := 1 - (cell13047 ⟨37,by decide⟩).lower)
        (by norm_num [cell13047]) (by norm_num [cell13047])
      exact ⟨E.1,E.2.trans (by norm_num [cell13047])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy38 (n := 13047) (by norm_num)
        (q := 1 - (cell13047 ⟨38,by decide⟩).lower)
        (by norm_num [cell13047]) (by norm_num [cell13047])
      exact ⟨E.1,E.2.trans (by norm_num [cell13047])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy39 (n := 13047) (by norm_num)
        (q := 1 - (cell13047 ⟨39,by decide⟩).lower)
        (by norm_num [cell13047]) (by norm_num [cell13047])
      exact ⟨E.1,E.2.trans (by norm_num [cell13047])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy40 (n := 13047) (by norm_num)
        (q := 1 - (cell13047 ⟨40,by decide⟩).lower)
        (by norm_num [cell13047]) (by norm_num [cell13047])
      exact ⟨E.1,E.2.trans (by norm_num [cell13047])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy41 (n := 13047) (by norm_num)
        (q := 1 - (cell13047 ⟨41,by decide⟩).lower)
        (by norm_num [cell13047]) (by norm_num [cell13047])
      exact ⟨E.1,E.2.trans (by norm_num [cell13047])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy42 (n := 13047) (by norm_num)
        (q := 1 - (cell13047 ⟨42,by decide⟩).lower)
        (by norm_num [cell13047]) (by norm_num [cell13047])
      exact ⟨E.1,E.2.trans (by norm_num [cell13047])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy43 (n := 13047) (by norm_num)
        (q := 1 - (cell13047 ⟨43,by decide⟩).lower)
        (by norm_num [cell13047]) (by norm_num [cell13047])
      exact ⟨E.1,E.2.trans (by norm_num [cell13047])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy44 (n := 13047) (by norm_num)
        (q := 1 - (cell13047 ⟨44,by decide⟩).lower)
        (by norm_num [cell13047]) (by norm_num [cell13047])
      exact ⟨E.1,E.2.trans (by norm_num [cell13047])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy45 (n := 13047) (by norm_num)
        (q := 1 - (cell13047 ⟨45,by decide⟩).lower)
        (by norm_num [cell13047]) (by norm_num [cell13047])
      exact ⟨E.1,E.2.trans (by norm_num [cell13047])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy46 (n := 13047) (by norm_num)
        (q := 1 - (cell13047 ⟨46,by decide⟩).lower)
        (by norm_num [cell13047]) (by norm_num [cell13047])
      exact ⟨E.1,E.2.trans (by norm_num [cell13047])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy47 (n := 13047) (by norm_num)
        (q := 1 - (cell13047 ⟨47,by decide⟩).lower)
        (by norm_num [cell13047]) (by norm_num [cell13047])
      exact ⟨E.1,E.2.trans (by norm_num [cell13047])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy48 (n := 13047) (by norm_num)
        (q := 1 - (cell13047 ⟨48,by decide⟩).lower)
        (by norm_num [cell13047]) (by norm_num [cell13047])
      exact ⟨E.1,E.2.trans (by norm_num [cell13047])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy49 (n := 13047) (by norm_num)
        (q := 1 - (cell13047 ⟨49,by decide⟩).lower)
        (by norm_num [cell13047]) (by norm_num [cell13047])
      exact ⟨E.1,E.2.trans (by norm_num [cell13047])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy50 (n := 13047) (by norm_num)
        (q := 1 - (cell13047 ⟨50,by decide⟩).lower)
        (by norm_num [cell13047]) (by norm_num [cell13047])
      exact ⟨E.1,E.2.trans (by norm_num [cell13047])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy51 (n := 13047) (by norm_num)
        (q := 1 - (cell13047 ⟨51,by decide⟩).lower)
        (by norm_num [cell13047]) (by norm_num [cell13047])
      exact ⟨E.1,E.2.trans (by norm_num [cell13047])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy52 (n := 13047) (by norm_num)
        (q := 1 - (cell13047 ⟨52,by decide⟩).lower)
        (by norm_num [cell13047]) (by norm_num [cell13047])
      exact ⟨E.1,E.2.trans (by norm_num [cell13047])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13047

/-! Source-cell containment and simple scalar guards at 13047. -/
namespace BstLean.Part269.N13047
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13047)
open BstLean.Part268 (cell13047)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13047 ⟨10,by decide⟩).lower ∧ (cell13047 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13047 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13047 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13047 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13047 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13047 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13047,cell13047,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13047 ⟨11,by decide⟩).lower ∧ (cell13047 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13047 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13047 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13047 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13047 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13047 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13047,cell13047,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13047 ⟨12,by decide⟩).lower ∧ (cell13047 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13047 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13047 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13047 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13047 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13047 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13047,cell13047,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13047 ⟨13,by decide⟩).lower ∧ (cell13047 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13047 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13047 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13047 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13047 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13047 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13047,cell13047,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13047 ⟨14,by decide⟩).lower ∧ (cell13047 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13047 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13047 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13047 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13047 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13047 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13047,cell13047,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13047 ⟨15,by decide⟩).lower ∧ (cell13047 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13047 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13047 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13047 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13047 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13047 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13047,cell13047,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13047 ⟨16,by decide⟩).lower ∧ (cell13047 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13047 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13047 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13047 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13047 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13047 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13047,cell13047,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13047 ⟨17,by decide⟩).lower ∧ (cell13047 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13047 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13047 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13047 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13047 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13047 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13047,cell13047,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13047 ⟨18,by decide⟩).lower ∧ (cell13047 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13047 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13047 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13047 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13047 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13047 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13047,cell13047,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13047 ⟨19,by decide⟩).lower ∧ (cell13047 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13047 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13047 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13047 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13047 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13047 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13047,cell13047,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13047 ⟨20,by decide⟩).lower ∧ (cell13047 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13047 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13047 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13047 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13047 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13047 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13047,cell13047,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13047 ⟨21,by decide⟩).lower ∧ (cell13047 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13047 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13047 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13047 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13047 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13047 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13047,cell13047,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13047 ⟨22,by decide⟩).lower ∧ (cell13047 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13047 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13047 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13047 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13047 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13047 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13047,cell13047,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13047 ⟨23,by decide⟩).lower ∧ (cell13047 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13047 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13047 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13047 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13047 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13047 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13047,cell13047,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13047 ⟨24,by decide⟩).lower ∧ (cell13047 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13047 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13047 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13047 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13047 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13047 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13047,cell13047,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13047 ⟨25,by decide⟩).lower ∧ (cell13047 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13047 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13047 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13047 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13047 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13047 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13047,cell13047,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13047 ⟨26,by decide⟩).lower ∧ (cell13047 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13047 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13047 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13047 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13047 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13047 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13047,cell13047,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13047 ⟨27,by decide⟩).lower ∧ (cell13047 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13047 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13047 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13047 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13047 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13047 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13047,cell13047,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13047 ⟨28,by decide⟩).lower ∧ (cell13047 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13047 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13047 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13047 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13047 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13047 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13047,cell13047,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13047 ⟨29,by decide⟩).lower ∧ (cell13047 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13047 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13047 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13047 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13047 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13047 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13047,cell13047,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13047 ⟨30,by decide⟩).lower ∧ (cell13047 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13047 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13047 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13047 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13047 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13047 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13047,cell13047,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13047 ⟨31,by decide⟩).lower ∧ (cell13047 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13047 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13047 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13047 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13047 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13047 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13047,cell13047,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13047 ⟨32,by decide⟩).lower ∧ (cell13047 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13047 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13047 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13047 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13047 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13047 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13047,cell13047,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13047 ⟨33,by decide⟩).lower ∧ (cell13047 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13047 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13047 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13047 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13047 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13047 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13047,cell13047,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13047 ⟨34,by decide⟩).lower ∧ (cell13047 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13047 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13047 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13047 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13047 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13047 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13047,cell13047,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13047 ⟨35,by decide⟩).lower ∧ (cell13047 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13047 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13047 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13047 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13047 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13047 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13047,cell13047,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13047 ⟨36,by decide⟩).lower ∧ (cell13047 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13047 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13047 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13047 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13047 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13047 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13047,cell13047,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13047 ⟨37,by decide⟩).lower ∧ (cell13047 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13047 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13047 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13047 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13047 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13047 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13047,cell13047,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13047 ⟨38,by decide⟩).lower ∧ (cell13047 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13047 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13047 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13047 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13047 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13047 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13047,cell13047,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13047 ⟨39,by decide⟩).lower ∧ (cell13047 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13047 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13047 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13047 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13047 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13047 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13047,cell13047,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13047 ⟨40,by decide⟩).lower ∧ (cell13047 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13047 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13047 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13047 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13047 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13047 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13047,cell13047,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13047 ⟨41,by decide⟩).lower ∧ (cell13047 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13047 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13047 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13047 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13047 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13047 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13047,cell13047,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13047 ⟨42,by decide⟩).lower ∧ (cell13047 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13047 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13047 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13047 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13047 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13047 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13047,cell13047,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13047 ⟨43,by decide⟩).lower ∧ (cell13047 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13047 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13047 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13047 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13047 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13047 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13047,cell13047,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13047 ⟨44,by decide⟩).lower ∧ (cell13047 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13047 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13047 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13047 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13047 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13047 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13047,cell13047,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13047 ⟨45,by decide⟩).lower ∧ (cell13047 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13047 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13047 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13047 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13047 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13047 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13047,cell13047,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13047 ⟨46,by decide⟩).lower ∧ (cell13047 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13047 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13047 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13047 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13047 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13047 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13047,cell13047,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13047 ⟨47,by decide⟩).lower ∧ (cell13047 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13047 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13047 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13047 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13047 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13047 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13047,cell13047,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13047 ⟨48,by decide⟩).lower ∧ (cell13047 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13047 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13047 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13047 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13047 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13047 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13047,cell13047,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13047 ⟨49,by decide⟩).lower ∧ (cell13047 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13047 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13047 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13047 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13047 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13047 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13047,cell13047,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13047 ⟨50,by decide⟩).lower ∧ (cell13047 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13047 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13047 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13047 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13047 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13047 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13047,cell13047,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13047 ⟨51,by decide⟩).lower ∧ (cell13047 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13047 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13047 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13047 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13047 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13047 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13047,cell13047,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13047 ⟨52,by decide⟩).lower ∧ (cell13047 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13047 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13047 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13047 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13047 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13047 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13047,cell13047,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13047 i).lower ∧
    (cell13047 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13047 i).upper ≤ (0.532 : ℝ) ∧
    (cell13047 i).centre ≤ (0.1 : ℝ) ∧ (cell13047 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13047 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13047 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13047

/-! The local source numeric instances at 13047 have no network premises. -/
namespace BstLean.Part269.N13047
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13047)
open BstLean.Part268 (cell13047)

noncomputable def sourceNumerics13047 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13047 (cell13047 i)
      scalarRow13047.M scalarRow13047.H scalarRow13047.xi := by
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
    energy_allowance := scalarRow13047.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13047]
    centre_nonneg := (scalarRow13047.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D27.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13047])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13047
/-! Actual 13048 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13048
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13048 ≤ (1.035324292609 : ℝ) := by
  have hr : (114.227842490349 : ℝ) ≤ √(13048 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.227842490349 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13048 13048 (11 / 1000) ≤
    (0.008368248146 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13048) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.227842490349 : ℝ) ≤ √(13048 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13048)
  have hdiv : K / √(13048 : ℝ) ≤ K / 114.227842490349 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.227842490349 ≤ (0.008368248146 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13048.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13048 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13048 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13048 := gPlus_lower 13048
end BstLean.Part269.N13048

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13048
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035324292608 : ℝ) ≤ wn 13048 := by
  have hn : √(13048 : ℝ) ≤ 114.227842490350 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13048 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.227842490350 ≤ 2 / √(13048 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000245048240 : ℝ) ≤ rhoBar 13048 BstLean.Part154.csC ∧
    rhoBar 13048 BstLean.Part154.csC ≤ 0.000245048619 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035324292608 : ℝ) / (1.295212 * 13048) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035324292609 : ℝ) / (1.29521 * 13048) := by gcongr
      _ ≤ (0.000245048619 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13048 BstLean.Part154.csC) ≤ 0.000980254525 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13048 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13048 BstLean.Part154.csC) (piBar (rhoBar 13048 BstLean.Part154.csC)) ≤ 0.000187169552 ∧
    cc1 (rhoBar 13048 BstLean.Part154.csC) (piBar (rhoBar 13048 BstLean.Part154.csC)) ≤ 0.000119097277 ∧
    cc2 (rhoBar 13048 BstLean.Part154.csC) ≤ 0.000069136941 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13048 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13048 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13048 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13048 BstLean.Part154.csC * nuR (rhoBar 13048 BstLean.Part154.csC)) ≤ 0.000490112251 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000245048619 : ℝ) * 0.000980254525 := by gcongr
      _ ≤ (0.000490112251 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13048 BstLean.Part154.csC) * nuR (rhoBar 13048 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000980254525 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13048 BstLean.Part154.csC) * rhoBar 13048 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000245048619 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000245048619 / 2 + 0.399 * 0.000980254525 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000187169552 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000490112251 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119097277 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000245048619 / 1.414213562 := by gcongr
      _ ≤ (0.000069136941 : ℝ) := by norm_num

end BstLean.Part269.N13048

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13048
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13048 BstLean.Part154.csC) (piBar (rhoBar 13048 BstLean.Part154.csC)) ≤ 1.51289E-7 := by
  have hr0 : 0 ≤ rhoBar 13048 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13048 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13048 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13048 BstLean.Part154.csC) (piBar (rhoBar 13048 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13048 BstLean.Part154.csC) (piBar (rhoBar 13048 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13048 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000187169552 : ℝ) ^ 2 + 0.000119097277 ^ 2 + 3 * 0.000069136941 ^ 2 +
        2 * 0.797885 * 0.000187169552 * 0.000119097277 + 2 * 0.000187169552 * 0.000069136941 +
        4 * 0.797885 * 0.000119097277 * 0.000069136941 := by gcongr
    _ ≤ (1.51289E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13048 BstLean.Part154.csC Θ ≤ 0.002556772935 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13048 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13048 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13048 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13048 BstLean.Part154.csC) (piBar (rhoBar 13048 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13048 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035324292609 * 1.51289E-7 / (0.000245048240 : ℝ) := by gcongr
    _ ≤ 0.002556772935 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13048 BstLean.Part154.csC Θ ≤ 0.002835539329 + 0.000646054073 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13048 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13048 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13048 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035324292609 : ℝ) * ((2 * Θ * 0.000245048619 +
        (6863 / 10000) * 0.000245048619 * 13048 * 0.000980254525) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002835539329 + 0.000646054073 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13048 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13048 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13048 0.011 Θ ∧ gammaRatio 13048 0.011 Θ ≤ 0.000084241379 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13048 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035324292609 : ℝ) * 0.525 / ((1 - 0.011) * 13048) := by gcongr
      _ ≤ (0.000084241379 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13048 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13048 0.011 Θ) :=
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
    badAllowance 13048 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000383431726 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13048 BstLean.Part154.csC) 1.22 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 2 (rhoBar 13048 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13048 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13048 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13048 0.011 Θ) 1.12 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 1 (gammaRatio 13048 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13048 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13048 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13048 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13048 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035324292609 : ℝ) * 13048 *
        (1.3781E-8 / 1.1045361 + 1.6832E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000383431726 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13048 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003218971055 + 0.003202827008 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13048

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13048
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13048 BstLean.Part154.csC) (piBar (rhoBar 13048 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13048 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13048 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13048 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13048 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13048 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13048 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13048 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13048 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13048 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13048 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13048 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13048 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13048 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13048 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051772146675 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13048) ≤ 0.010454872955 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13048 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035324292609)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010454872955 + 2 * 0.737676 / 13048) := by gcongr
    _ ≤ (0.051772146675 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13048 12 ≤ 0.0015 := by
  exact BstLean.Part269.S27.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13048

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13048
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560518886151 : ℝ) ≤ plow 13048 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13048) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052407055235)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001342305791) : eMP 13048 0.011 xi bn ≤ 0.001156059455 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13048 : ℝ) * (1 - 0.011))) ≤ 0.000571650480 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001342305791 / (13048 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000571650480 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000571650480 : ℝ) + 3.141593 * 0.052407055235 / (13048 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001156059455 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052407055235)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001342305791) : PiBarMP 13048 12 0.011 xi bn ≤ 0.159064872900 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13048 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036637491604 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.597852092370 : ℝ) ≤ √((13048 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.227842490349 : ℝ) ≤ √(13048 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13048) ≤ 0.121970335420 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036637491604 + 0.052407055235 * 1.772454 / (2 * (113.597852092370 : ℝ))) * (1 + 0.001156059455) +
        8 / (13048 * 114.227842490349) + 0.121970335420 := by gcongr
    _ ≤ (0.159064872900 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052407055235)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001342305791) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280698019471) :
    parallelOracle 13048 0.011 xi bn cd ≤ 0.160028847762 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13048 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13048 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560518886151 : ℝ) ≤ plow 13048 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.227842490349 : ℝ) ≤ √(13048 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280698019471 : ℝ) / (2 * 0.560518886151 * 114.227842490349)) * 0.159064872900 +
        0.280698019471 ^ 2 / (2 * 0.560518886151 * 114.227842490349) := by gcongr
    _ ≤ (0.160028847762 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052407055235) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001342305791)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280698019471) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13048 13048 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560518886151 : ℝ) ≤ plow 13048 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.227842490349 : ℝ) ≤ √(13048 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13048 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13048 Θ 1.22 ≤ 0.011609258051 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.227842490349 := by gcongr <;> linarith
      _ ≤ (0.011609258051 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13048 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13048 13048 0.011 ≤ 0.008368248146 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13048 13048 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13048 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13048 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13048 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13048 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160028847762 + 0.011609258051 + (0.008368248146 : ℝ) *
        (1 + 2 * (0.280698019471 + 0.011609258051) / (0.560518886151 * 114.227842490349))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13048]

end BstLean.Part269.N13048

/-! The original eight local profiles supply actual 13048 moment certificates. -/
namespace BstLean.Part269.N13048
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13048 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13048 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13048 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052407055235 ∧
    0 ≤ bN 13048 BstLean.Part154.csC (groupTheta g) ∧ bN 13048 BstLean.Part154.csC (groupTheta g) ≤ 0.001342305791 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13048 13048 0.011
      (momentAllowance 13048 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13048 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13048 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13048 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13048 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13048 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228925872796 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13048 0.011
      (momentAllowance 13048 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13048 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13048
/-! The actual computed-centre upper energy formula at 13048. -/
namespace BstLean.Part269.N13048
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13048

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13048
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13048)
open BstLean.Part268 (cell13048)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084535338102
  | 2 => 0.085462384666
  | 3 => 0.086385395556
  | 4 => 0.087305277637
  | 5 => 0.088223142674
  | 6 => 0.089140339606
  | 7 => 0.090058490191
  | 8 => 0.090979528159
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13048 13048 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13048 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N13048

/-! Actual upper energy certificates on all 43 source endpoints at 13048. -/
namespace BstLean.Part269.N13048
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13048)
open BstLean.Part268 (cell13048)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13048 (gMinus 13048) (1 - (cell13048 i).lower) ≤ 1 ∧
    energyUpper 13048 (gMinus 13048) (BstLean.Part211.gPlus 13048)
      (finiteEnergy 13048 13048 0.011) (1 - (cell13048 i).lower) ≤
      (cell13048 i).energy := by
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
      have E := BstLean.Part269.S27.uniformEnergy10 (n := 13048) (by norm_num)
        (q := 1 - (cell13048 ⟨10,by decide⟩).lower)
        (by norm_num [cell13048]) (by norm_num [cell13048])
      exact ⟨E.1,E.2.trans (by norm_num [cell13048])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy11 (n := 13048) (by norm_num)
        (q := 1 - (cell13048 ⟨11,by decide⟩).lower)
        (by norm_num [cell13048]) (by norm_num [cell13048])
      exact ⟨E.1,E.2.trans (by norm_num [cell13048])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy12 (n := 13048) (by norm_num)
        (q := 1 - (cell13048 ⟨12,by decide⟩).lower)
        (by norm_num [cell13048]) (by norm_num [cell13048])
      exact ⟨E.1,E.2.trans (by norm_num [cell13048])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy13 (n := 13048) (by norm_num)
        (q := 1 - (cell13048 ⟨13,by decide⟩).lower)
        (by norm_num [cell13048]) (by norm_num [cell13048])
      exact ⟨E.1,E.2.trans (by norm_num [cell13048])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy14 (n := 13048) (by norm_num)
        (q := 1 - (cell13048 ⟨14,by decide⟩).lower)
        (by norm_num [cell13048]) (by norm_num [cell13048])
      exact ⟨E.1,E.2.trans (by norm_num [cell13048])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy15 (n := 13048) (by norm_num)
        (q := 1 - (cell13048 ⟨15,by decide⟩).lower)
        (by norm_num [cell13048]) (by norm_num [cell13048])
      exact ⟨E.1,E.2.trans (by norm_num [cell13048])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy16 (n := 13048) (by norm_num)
        (q := 1 - (cell13048 ⟨16,by decide⟩).lower)
        (by norm_num [cell13048]) (by norm_num [cell13048])
      exact ⟨E.1,E.2.trans (by norm_num [cell13048])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy17 (n := 13048) (by norm_num)
        (q := 1 - (cell13048 ⟨17,by decide⟩).lower)
        (by norm_num [cell13048]) (by norm_num [cell13048])
      exact ⟨E.1,E.2.trans (by norm_num [cell13048])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy18 (n := 13048) (by norm_num)
        (q := 1 - (cell13048 ⟨18,by decide⟩).lower)
        (by norm_num [cell13048]) (by norm_num [cell13048])
      exact ⟨E.1,E.2.trans (by norm_num [cell13048])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy19 (n := 13048) (by norm_num)
        (q := 1 - (cell13048 ⟨19,by decide⟩).lower)
        (by norm_num [cell13048]) (by norm_num [cell13048])
      exact ⟨E.1,E.2.trans (by norm_num [cell13048])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy20 (n := 13048) (by norm_num)
        (q := 1 - (cell13048 ⟨20,by decide⟩).lower)
        (by norm_num [cell13048]) (by norm_num [cell13048])
      exact ⟨E.1,E.2.trans (by norm_num [cell13048])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy21 (n := 13048) (by norm_num)
        (q := 1 - (cell13048 ⟨21,by decide⟩).lower)
        (by norm_num [cell13048]) (by norm_num [cell13048])
      exact ⟨E.1,E.2.trans (by norm_num [cell13048])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy22 (n := 13048) (by norm_num)
        (q := 1 - (cell13048 ⟨22,by decide⟩).lower)
        (by norm_num [cell13048]) (by norm_num [cell13048])
      exact ⟨E.1,E.2.trans (by norm_num [cell13048])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy23 (n := 13048) (by norm_num)
        (q := 1 - (cell13048 ⟨23,by decide⟩).lower)
        (by norm_num [cell13048]) (by norm_num [cell13048])
      exact ⟨E.1,E.2.trans (by norm_num [cell13048])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy24 (n := 13048) (by norm_num)
        (q := 1 - (cell13048 ⟨24,by decide⟩).lower)
        (by norm_num [cell13048]) (by norm_num [cell13048])
      exact ⟨E.1,E.2.trans (by norm_num [cell13048])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy25 (n := 13048) (by norm_num)
        (q := 1 - (cell13048 ⟨25,by decide⟩).lower)
        (by norm_num [cell13048]) (by norm_num [cell13048])
      exact ⟨E.1,E.2.trans (by norm_num [cell13048])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy26 (n := 13048) (by norm_num)
        (q := 1 - (cell13048 ⟨26,by decide⟩).lower)
        (by norm_num [cell13048]) (by norm_num [cell13048])
      exact ⟨E.1,E.2.trans (by norm_num [cell13048])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy27 (n := 13048) (by norm_num)
        (q := 1 - (cell13048 ⟨27,by decide⟩).lower)
        (by norm_num [cell13048]) (by norm_num [cell13048])
      exact ⟨E.1,E.2.trans (by norm_num [cell13048])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy28 (n := 13048) (by norm_num)
        (q := 1 - (cell13048 ⟨28,by decide⟩).lower)
        (by norm_num [cell13048]) (by norm_num [cell13048])
      exact ⟨E.1,E.2.trans (by norm_num [cell13048])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy29 (n := 13048) (by norm_num)
        (q := 1 - (cell13048 ⟨29,by decide⟩).lower)
        (by norm_num [cell13048]) (by norm_num [cell13048])
      exact ⟨E.1,E.2.trans (by norm_num [cell13048])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy30 (n := 13048) (by norm_num)
        (q := 1 - (cell13048 ⟨30,by decide⟩).lower)
        (by norm_num [cell13048]) (by norm_num [cell13048])
      exact ⟨E.1,E.2.trans (by norm_num [cell13048])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy31 (n := 13048) (by norm_num)
        (q := 1 - (cell13048 ⟨31,by decide⟩).lower)
        (by norm_num [cell13048]) (by norm_num [cell13048])
      exact ⟨E.1,E.2.trans (by norm_num [cell13048])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy32 (n := 13048) (by norm_num)
        (q := 1 - (cell13048 ⟨32,by decide⟩).lower)
        (by norm_num [cell13048]) (by norm_num [cell13048])
      exact ⟨E.1,E.2.trans (by norm_num [cell13048])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy33 (n := 13048) (by norm_num)
        (q := 1 - (cell13048 ⟨33,by decide⟩).lower)
        (by norm_num [cell13048]) (by norm_num [cell13048])
      exact ⟨E.1,E.2.trans (by norm_num [cell13048])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy34 (n := 13048) (by norm_num)
        (q := 1 - (cell13048 ⟨34,by decide⟩).lower)
        (by norm_num [cell13048]) (by norm_num [cell13048])
      exact ⟨E.1,E.2.trans (by norm_num [cell13048])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy35 (n := 13048) (by norm_num)
        (q := 1 - (cell13048 ⟨35,by decide⟩).lower)
        (by norm_num [cell13048]) (by norm_num [cell13048])
      exact ⟨E.1,E.2.trans (by norm_num [cell13048])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy36 (n := 13048) (by norm_num)
        (q := 1 - (cell13048 ⟨36,by decide⟩).lower)
        (by norm_num [cell13048]) (by norm_num [cell13048])
      exact ⟨E.1,E.2.trans (by norm_num [cell13048])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy37 (n := 13048) (by norm_num)
        (q := 1 - (cell13048 ⟨37,by decide⟩).lower)
        (by norm_num [cell13048]) (by norm_num [cell13048])
      exact ⟨E.1,E.2.trans (by norm_num [cell13048])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy38 (n := 13048) (by norm_num)
        (q := 1 - (cell13048 ⟨38,by decide⟩).lower)
        (by norm_num [cell13048]) (by norm_num [cell13048])
      exact ⟨E.1,E.2.trans (by norm_num [cell13048])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy39 (n := 13048) (by norm_num)
        (q := 1 - (cell13048 ⟨39,by decide⟩).lower)
        (by norm_num [cell13048]) (by norm_num [cell13048])
      exact ⟨E.1,E.2.trans (by norm_num [cell13048])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy40 (n := 13048) (by norm_num)
        (q := 1 - (cell13048 ⟨40,by decide⟩).lower)
        (by norm_num [cell13048]) (by norm_num [cell13048])
      exact ⟨E.1,E.2.trans (by norm_num [cell13048])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy41 (n := 13048) (by norm_num)
        (q := 1 - (cell13048 ⟨41,by decide⟩).lower)
        (by norm_num [cell13048]) (by norm_num [cell13048])
      exact ⟨E.1,E.2.trans (by norm_num [cell13048])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy42 (n := 13048) (by norm_num)
        (q := 1 - (cell13048 ⟨42,by decide⟩).lower)
        (by norm_num [cell13048]) (by norm_num [cell13048])
      exact ⟨E.1,E.2.trans (by norm_num [cell13048])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy43 (n := 13048) (by norm_num)
        (q := 1 - (cell13048 ⟨43,by decide⟩).lower)
        (by norm_num [cell13048]) (by norm_num [cell13048])
      exact ⟨E.1,E.2.trans (by norm_num [cell13048])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy44 (n := 13048) (by norm_num)
        (q := 1 - (cell13048 ⟨44,by decide⟩).lower)
        (by norm_num [cell13048]) (by norm_num [cell13048])
      exact ⟨E.1,E.2.trans (by norm_num [cell13048])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy45 (n := 13048) (by norm_num)
        (q := 1 - (cell13048 ⟨45,by decide⟩).lower)
        (by norm_num [cell13048]) (by norm_num [cell13048])
      exact ⟨E.1,E.2.trans (by norm_num [cell13048])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy46 (n := 13048) (by norm_num)
        (q := 1 - (cell13048 ⟨46,by decide⟩).lower)
        (by norm_num [cell13048]) (by norm_num [cell13048])
      exact ⟨E.1,E.2.trans (by norm_num [cell13048])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy47 (n := 13048) (by norm_num)
        (q := 1 - (cell13048 ⟨47,by decide⟩).lower)
        (by norm_num [cell13048]) (by norm_num [cell13048])
      exact ⟨E.1,E.2.trans (by norm_num [cell13048])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy48 (n := 13048) (by norm_num)
        (q := 1 - (cell13048 ⟨48,by decide⟩).lower)
        (by norm_num [cell13048]) (by norm_num [cell13048])
      exact ⟨E.1,E.2.trans (by norm_num [cell13048])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy49 (n := 13048) (by norm_num)
        (q := 1 - (cell13048 ⟨49,by decide⟩).lower)
        (by norm_num [cell13048]) (by norm_num [cell13048])
      exact ⟨E.1,E.2.trans (by norm_num [cell13048])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy50 (n := 13048) (by norm_num)
        (q := 1 - (cell13048 ⟨50,by decide⟩).lower)
        (by norm_num [cell13048]) (by norm_num [cell13048])
      exact ⟨E.1,E.2.trans (by norm_num [cell13048])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy51 (n := 13048) (by norm_num)
        (q := 1 - (cell13048 ⟨51,by decide⟩).lower)
        (by norm_num [cell13048]) (by norm_num [cell13048])
      exact ⟨E.1,E.2.trans (by norm_num [cell13048])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy52 (n := 13048) (by norm_num)
        (q := 1 - (cell13048 ⟨52,by decide⟩).lower)
        (by norm_num [cell13048]) (by norm_num [cell13048])
      exact ⟨E.1,E.2.trans (by norm_num [cell13048])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13048

/-! Source-cell containment and simple scalar guards at 13048. -/
namespace BstLean.Part269.N13048
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13048)
open BstLean.Part268 (cell13048)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13048 ⟨10,by decide⟩).lower ∧ (cell13048 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13048 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13048 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13048 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13048 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13048 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13048,cell13048,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13048 ⟨11,by decide⟩).lower ∧ (cell13048 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13048 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13048 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13048 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13048 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13048 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13048,cell13048,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13048 ⟨12,by decide⟩).lower ∧ (cell13048 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13048 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13048 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13048 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13048 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13048 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13048,cell13048,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13048 ⟨13,by decide⟩).lower ∧ (cell13048 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13048 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13048 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13048 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13048 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13048 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13048,cell13048,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13048 ⟨14,by decide⟩).lower ∧ (cell13048 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13048 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13048 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13048 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13048 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13048 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13048,cell13048,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13048 ⟨15,by decide⟩).lower ∧ (cell13048 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13048 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13048 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13048 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13048 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13048 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13048,cell13048,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13048 ⟨16,by decide⟩).lower ∧ (cell13048 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13048 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13048 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13048 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13048 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13048 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13048,cell13048,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13048 ⟨17,by decide⟩).lower ∧ (cell13048 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13048 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13048 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13048 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13048 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13048 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13048,cell13048,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13048 ⟨18,by decide⟩).lower ∧ (cell13048 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13048 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13048 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13048 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13048 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13048 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13048,cell13048,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13048 ⟨19,by decide⟩).lower ∧ (cell13048 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13048 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13048 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13048 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13048 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13048 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13048,cell13048,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13048 ⟨20,by decide⟩).lower ∧ (cell13048 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13048 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13048 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13048 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13048 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13048 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13048,cell13048,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13048 ⟨21,by decide⟩).lower ∧ (cell13048 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13048 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13048 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13048 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13048 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13048 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13048,cell13048,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13048 ⟨22,by decide⟩).lower ∧ (cell13048 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13048 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13048 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13048 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13048 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13048 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13048,cell13048,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13048 ⟨23,by decide⟩).lower ∧ (cell13048 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13048 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13048 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13048 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13048 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13048 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13048,cell13048,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13048 ⟨24,by decide⟩).lower ∧ (cell13048 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13048 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13048 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13048 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13048 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13048 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13048,cell13048,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13048 ⟨25,by decide⟩).lower ∧ (cell13048 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13048 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13048 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13048 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13048 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13048 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13048,cell13048,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13048 ⟨26,by decide⟩).lower ∧ (cell13048 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13048 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13048 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13048 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13048 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13048 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13048,cell13048,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13048 ⟨27,by decide⟩).lower ∧ (cell13048 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13048 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13048 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13048 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13048 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13048 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13048,cell13048,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13048 ⟨28,by decide⟩).lower ∧ (cell13048 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13048 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13048 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13048 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13048 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13048 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13048,cell13048,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13048 ⟨29,by decide⟩).lower ∧ (cell13048 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13048 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13048 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13048 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13048 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13048 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13048,cell13048,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13048 ⟨30,by decide⟩).lower ∧ (cell13048 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13048 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13048 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13048 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13048 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13048 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13048,cell13048,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13048 ⟨31,by decide⟩).lower ∧ (cell13048 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13048 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13048 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13048 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13048 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13048 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13048,cell13048,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13048 ⟨32,by decide⟩).lower ∧ (cell13048 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13048 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13048 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13048 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13048 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13048 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13048,cell13048,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13048 ⟨33,by decide⟩).lower ∧ (cell13048 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13048 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13048 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13048 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13048 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13048 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13048,cell13048,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13048 ⟨34,by decide⟩).lower ∧ (cell13048 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13048 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13048 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13048 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13048 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13048 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13048,cell13048,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13048 ⟨35,by decide⟩).lower ∧ (cell13048 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13048 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13048 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13048 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13048 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13048 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13048,cell13048,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13048 ⟨36,by decide⟩).lower ∧ (cell13048 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13048 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13048 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13048 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13048 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13048 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13048,cell13048,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13048 ⟨37,by decide⟩).lower ∧ (cell13048 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13048 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13048 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13048 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13048 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13048 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13048,cell13048,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13048 ⟨38,by decide⟩).lower ∧ (cell13048 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13048 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13048 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13048 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13048 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13048 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13048,cell13048,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13048 ⟨39,by decide⟩).lower ∧ (cell13048 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13048 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13048 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13048 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13048 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13048 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13048,cell13048,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13048 ⟨40,by decide⟩).lower ∧ (cell13048 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13048 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13048 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13048 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13048 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13048 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13048,cell13048,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13048 ⟨41,by decide⟩).lower ∧ (cell13048 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13048 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13048 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13048 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13048 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13048 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13048,cell13048,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13048 ⟨42,by decide⟩).lower ∧ (cell13048 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13048 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13048 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13048 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13048 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13048 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13048,cell13048,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13048 ⟨43,by decide⟩).lower ∧ (cell13048 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13048 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13048 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13048 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13048 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13048 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13048,cell13048,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13048 ⟨44,by decide⟩).lower ∧ (cell13048 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13048 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13048 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13048 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13048 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13048 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13048,cell13048,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13048 ⟨45,by decide⟩).lower ∧ (cell13048 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13048 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13048 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13048 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13048 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13048 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13048,cell13048,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13048 ⟨46,by decide⟩).lower ∧ (cell13048 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13048 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13048 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13048 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13048 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13048 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13048,cell13048,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13048 ⟨47,by decide⟩).lower ∧ (cell13048 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13048 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13048 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13048 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13048 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13048 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13048,cell13048,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13048 ⟨48,by decide⟩).lower ∧ (cell13048 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13048 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13048 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13048 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13048 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13048 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13048,cell13048,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13048 ⟨49,by decide⟩).lower ∧ (cell13048 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13048 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13048 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13048 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13048 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13048 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13048,cell13048,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13048 ⟨50,by decide⟩).lower ∧ (cell13048 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13048 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13048 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13048 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13048 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13048 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13048,cell13048,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13048 ⟨51,by decide⟩).lower ∧ (cell13048 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13048 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13048 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13048 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13048 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13048 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13048,cell13048,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13048 ⟨52,by decide⟩).lower ∧ (cell13048 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13048 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13048 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13048 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13048 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13048 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13048,cell13048,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13048 i).lower ∧
    (cell13048 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13048 i).upper ≤ (0.532 : ℝ) ∧
    (cell13048 i).centre ≤ (0.1 : ℝ) ∧ (cell13048 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13048 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13048 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13048

/-! The local source numeric instances at 13048 have no network premises. -/
namespace BstLean.Part269.N13048
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13048)
open BstLean.Part268 (cell13048)

noncomputable def sourceNumerics13048 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13048 (cell13048 i)
      scalarRow13048.M scalarRow13048.H scalarRow13048.xi := by
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
    energy_allowance := scalarRow13048.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13048]
    centre_nonneg := (scalarRow13048.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D27.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13048])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13048
/-! Actual 13049 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13049
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13049 ≤ (1.035322927312 : ℝ) := by
  have hr : (114.232219623011 : ℝ) ≤ √(13049 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.232219623011 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13049 13049 (11 / 1000) ≤
    (0.008367927490 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13049) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.232219623011 : ℝ) ≤ √(13049 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13049)
  have hdiv : K / √(13049 : ℝ) ≤ K / 114.232219623011 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.232219623011 ≤ (0.008367927490 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13049.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13049 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13049 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13049 := gPlus_lower 13049
end BstLean.Part269.N13049

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13049
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035322927311 : ℝ) ≤ wn 13049 := by
  have hn : √(13049 : ℝ) ≤ 114.232219623012 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13049 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.232219623012 ≤ 2 / √(13049 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000245029138 : ℝ) ≤ rhoBar 13049 BstLean.Part154.csC ∧
    rhoBar 13049 BstLean.Part154.csC ≤ 0.000245029517 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035322927311 : ℝ) / (1.295212 * 13049) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035322927312 : ℝ) / (1.29521 * 13049) := by gcongr
      _ ≤ (0.000245029517 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13049 BstLean.Part154.csC) ≤ 0.000980178108 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13049 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13049 BstLean.Part154.csC) (piBar (rhoBar 13049 BstLean.Part154.csC)) ≤ 0.000187154961 ∧
    cc1 (rhoBar 13049 BstLean.Part154.csC) (piBar (rhoBar 13049 BstLean.Part154.csC)) ≤ 0.000119087993 ∧
    cc2 (rhoBar 13049 BstLean.Part154.csC) ≤ 0.000069131552 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13049 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13049 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13049 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13049 BstLean.Part154.csC * nuR (rhoBar 13049 BstLean.Part154.csC)) ≤ 0.000490074044 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000245029517 : ℝ) * 0.000980178108 := by gcongr
      _ ≤ (0.000490074044 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13049 BstLean.Part154.csC) * nuR (rhoBar 13049 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000980178108 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13049 BstLean.Part154.csC) * rhoBar 13049 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000245029517 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000245029517 / 2 + 0.399 * 0.000980178108 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000187154961 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000490074044 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119087993 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000245029517 / 1.414213562 := by gcongr
      _ ≤ (0.000069131552 : ℝ) := by norm_num

end BstLean.Part269.N13049

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13049
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13049 BstLean.Part154.csC) (piBar (rhoBar 13049 BstLean.Part154.csC)) ≤ 1.51265E-7 := by
  have hr0 : 0 ≤ rhoBar 13049 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13049 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13049 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13049 BstLean.Part154.csC) (piBar (rhoBar 13049 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13049 BstLean.Part154.csC) (piBar (rhoBar 13049 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13049 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000187154961 : ℝ) ^ 2 + 0.000119087993 ^ 2 + 3 * 0.000069131552 ^ 2 +
        2 * 0.797885 * 0.000187154961 * 0.000119087993 + 2 * 0.000187154961 * 0.000069131552 +
        4 * 0.797885 * 0.000119087993 * 0.000069131552 := by gcongr
    _ ≤ (1.51265E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13049 BstLean.Part154.csC Θ ≤ 0.002556563255 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13049 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13049 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13049 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13049 BstLean.Part154.csC) (piBar (rhoBar 13049 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13049 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035322927312 * 1.51265E-7 / (0.000245029138 : ℝ) := by gcongr
    _ ≤ 0.002556563255 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13049 BstLean.Part154.csC Θ ≤ 0.002835310806 + 0.000646002860 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13049 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13049 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13049 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035322927312 : ℝ) * ((2 * Θ * 0.000245029517 +
        (6863 / 10000) * 0.000245029517 * 13049 * 0.000980178108) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002835310806 + 0.000646002860 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13049 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13049 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13049 0.011 Θ ∧ gammaRatio 13049 0.011 Θ ≤ 0.000084234812 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13049 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035322927312 : ℝ) * 0.525 / ((1 - 0.011) * 13049) := by gcongr
      _ ≤ (0.000084234812 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13049 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13049 0.011 Θ) :=
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
    badAllowance 13049 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000383431726 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13049 BstLean.Part154.csC) 1.22 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 2 (rhoBar 13049 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13049 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13049 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13049 0.011 Θ) 1.12 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 1 (gammaRatio 13049 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13049 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13049 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13049 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13049 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035322927312 : ℝ) * 13049 *
        (1.3781E-8 / 1.1045361 + 1.6832E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000383431726 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13049 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003218742532 + 0.003202566115 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13049

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13049
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13049 BstLean.Part154.csC) (piBar (rhoBar 13049 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13049 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13049 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13049 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13049 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13049 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13049 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13049 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13049 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13049 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13049 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13049 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13049 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13049 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13049 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051770141649 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13049) ≤ 0.010454472346 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13049 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035322927312)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010454472346 + 2 * 0.737676 / 13049) := by gcongr
    _ ≤ (0.051770141649 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13049 12 ≤ 0.0015 := by
  exact BstLean.Part269.S27.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13049

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13049
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560518928990 : ℝ) ≤ plow 13049 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13049) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052406689743)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001342195709) : eMP 13049 0.011 xi bn ≤ 0.001155967701 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13049 : ℝ) * (1 - 0.011))) ≤ 0.000571605136 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001342195709 / (13049 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000571605136 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000571605136 : ℝ) + 3.141593 * 0.052406689743 / (13049 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001155967701 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052406689743)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001342195709) : PiBarMP 13049 12 0.011 xi bn ≤ 0.159058672623 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13049 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036635989260 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.602205084232 : ℝ) ≤ √((13049 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.232219623011 : ℝ) ≤ √(13049 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13049) ≤ 0.121965661779 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036635989260 + 0.052406689743 * 1.772454 / (2 * (113.602205084232 : ℝ))) * (1 + 0.001155967701) +
        8 / (13049 * 114.232219623011) + 0.121965661779 := by gcongr
    _ ≤ (0.159058672623 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052406689743)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001342195709) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280695216167) :
    parallelOracle 13049 0.011 xi bn cd ≤ 0.160022581112 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13049 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13049 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560518928990 : ℝ) ≤ plow 13049 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.232219623011 : ℝ) ≤ √(13049 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280695216167 : ℝ) / (2 * 0.560518928990 * 114.232219623011)) * 0.159058672623 +
        0.280695216167 ^ 2 / (2 * 0.560518928990 * 114.232219623011) := by gcongr
    _ ≤ (0.160022581112 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052406689743) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001342195709)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280695216167) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13049 13049 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560518928990 : ℝ) ≤ plow 13049 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.232219623011 : ℝ) ≤ √(13049 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13049 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13049 Θ 1.22 ≤ 0.011608813209 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.232219623011 := by gcongr <;> linarith
      _ ≤ (0.011608813209 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13049 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13049 13049 0.011 ≤ 0.008367927490 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13049 13049 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13049 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13049 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13049 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13049 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160022581112 + 0.011608813209 + (0.008367927490 : ℝ) *
        (1 + 2 * (0.280695216167 + 0.011608813209) / (0.560518928990 * 114.232219623011))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13049]

end BstLean.Part269.N13049

/-! The original eight local profiles supply actual 13049 moment certificates. -/
namespace BstLean.Part269.N13049
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13049 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13049 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13049 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052406689743 ∧
    0 ≤ bN 13049 BstLean.Part154.csC (groupTheta g) ∧ bN 13049 BstLean.Part154.csC (groupTheta g) ≤ 0.001342195709 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13049 13049 0.011
      (momentAllowance 13049 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13049 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13049 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13049 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13049 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13049 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228925074518 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13049 0.011
      (momentAllowance 13049 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13049 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13049
/-! The actual computed-centre upper energy formula at 13049. -/
namespace BstLean.Part269.N13049
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13049

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13049
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13049)
open BstLean.Part268 (cell13049)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084532757794
  | 2 => 0.085459771137
  | 3 => 0.086382743871
  | 4 => 0.087302581695
  | 5 => 0.088220394999
  | 6 => 0.089137531097
  | 7 => 0.090055609859
  | 8 => 0.090976562816
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13049 13049 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13049 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N13049

/-! Actual upper energy certificates on all 43 source endpoints at 13049. -/
namespace BstLean.Part269.N13049
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13049)
open BstLean.Part268 (cell13049)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13049 (gMinus 13049) (1 - (cell13049 i).lower) ≤ 1 ∧
    energyUpper 13049 (gMinus 13049) (BstLean.Part211.gPlus 13049)
      (finiteEnergy 13049 13049 0.011) (1 - (cell13049 i).lower) ≤
      (cell13049 i).energy := by
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
      have E := BstLean.Part269.S27.uniformEnergy10 (n := 13049) (by norm_num)
        (q := 1 - (cell13049 ⟨10,by decide⟩).lower)
        (by norm_num [cell13049]) (by norm_num [cell13049])
      exact ⟨E.1,E.2.trans (by norm_num [cell13049])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy11 (n := 13049) (by norm_num)
        (q := 1 - (cell13049 ⟨11,by decide⟩).lower)
        (by norm_num [cell13049]) (by norm_num [cell13049])
      exact ⟨E.1,E.2.trans (by norm_num [cell13049])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy12 (n := 13049) (by norm_num)
        (q := 1 - (cell13049 ⟨12,by decide⟩).lower)
        (by norm_num [cell13049]) (by norm_num [cell13049])
      exact ⟨E.1,E.2.trans (by norm_num [cell13049])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy13 (n := 13049) (by norm_num)
        (q := 1 - (cell13049 ⟨13,by decide⟩).lower)
        (by norm_num [cell13049]) (by norm_num [cell13049])
      exact ⟨E.1,E.2.trans (by norm_num [cell13049])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy14 (n := 13049) (by norm_num)
        (q := 1 - (cell13049 ⟨14,by decide⟩).lower)
        (by norm_num [cell13049]) (by norm_num [cell13049])
      exact ⟨E.1,E.2.trans (by norm_num [cell13049])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy15 (n := 13049) (by norm_num)
        (q := 1 - (cell13049 ⟨15,by decide⟩).lower)
        (by norm_num [cell13049]) (by norm_num [cell13049])
      exact ⟨E.1,E.2.trans (by norm_num [cell13049])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy16 (n := 13049) (by norm_num)
        (q := 1 - (cell13049 ⟨16,by decide⟩).lower)
        (by norm_num [cell13049]) (by norm_num [cell13049])
      exact ⟨E.1,E.2.trans (by norm_num [cell13049])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy17 (n := 13049) (by norm_num)
        (q := 1 - (cell13049 ⟨17,by decide⟩).lower)
        (by norm_num [cell13049]) (by norm_num [cell13049])
      exact ⟨E.1,E.2.trans (by norm_num [cell13049])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy18 (n := 13049) (by norm_num)
        (q := 1 - (cell13049 ⟨18,by decide⟩).lower)
        (by norm_num [cell13049]) (by norm_num [cell13049])
      exact ⟨E.1,E.2.trans (by norm_num [cell13049])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy19 (n := 13049) (by norm_num)
        (q := 1 - (cell13049 ⟨19,by decide⟩).lower)
        (by norm_num [cell13049]) (by norm_num [cell13049])
      exact ⟨E.1,E.2.trans (by norm_num [cell13049])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy20 (n := 13049) (by norm_num)
        (q := 1 - (cell13049 ⟨20,by decide⟩).lower)
        (by norm_num [cell13049]) (by norm_num [cell13049])
      exact ⟨E.1,E.2.trans (by norm_num [cell13049])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy21 (n := 13049) (by norm_num)
        (q := 1 - (cell13049 ⟨21,by decide⟩).lower)
        (by norm_num [cell13049]) (by norm_num [cell13049])
      exact ⟨E.1,E.2.trans (by norm_num [cell13049])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy22 (n := 13049) (by norm_num)
        (q := 1 - (cell13049 ⟨22,by decide⟩).lower)
        (by norm_num [cell13049]) (by norm_num [cell13049])
      exact ⟨E.1,E.2.trans (by norm_num [cell13049])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy23 (n := 13049) (by norm_num)
        (q := 1 - (cell13049 ⟨23,by decide⟩).lower)
        (by norm_num [cell13049]) (by norm_num [cell13049])
      exact ⟨E.1,E.2.trans (by norm_num [cell13049])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy24 (n := 13049) (by norm_num)
        (q := 1 - (cell13049 ⟨24,by decide⟩).lower)
        (by norm_num [cell13049]) (by norm_num [cell13049])
      exact ⟨E.1,E.2.trans (by norm_num [cell13049])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy25 (n := 13049) (by norm_num)
        (q := 1 - (cell13049 ⟨25,by decide⟩).lower)
        (by norm_num [cell13049]) (by norm_num [cell13049])
      exact ⟨E.1,E.2.trans (by norm_num [cell13049])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy26 (n := 13049) (by norm_num)
        (q := 1 - (cell13049 ⟨26,by decide⟩).lower)
        (by norm_num [cell13049]) (by norm_num [cell13049])
      exact ⟨E.1,E.2.trans (by norm_num [cell13049])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy27 (n := 13049) (by norm_num)
        (q := 1 - (cell13049 ⟨27,by decide⟩).lower)
        (by norm_num [cell13049]) (by norm_num [cell13049])
      exact ⟨E.1,E.2.trans (by norm_num [cell13049])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy28 (n := 13049) (by norm_num)
        (q := 1 - (cell13049 ⟨28,by decide⟩).lower)
        (by norm_num [cell13049]) (by norm_num [cell13049])
      exact ⟨E.1,E.2.trans (by norm_num [cell13049])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy29 (n := 13049) (by norm_num)
        (q := 1 - (cell13049 ⟨29,by decide⟩).lower)
        (by norm_num [cell13049]) (by norm_num [cell13049])
      exact ⟨E.1,E.2.trans (by norm_num [cell13049])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy30 (n := 13049) (by norm_num)
        (q := 1 - (cell13049 ⟨30,by decide⟩).lower)
        (by norm_num [cell13049]) (by norm_num [cell13049])
      exact ⟨E.1,E.2.trans (by norm_num [cell13049])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy31 (n := 13049) (by norm_num)
        (q := 1 - (cell13049 ⟨31,by decide⟩).lower)
        (by norm_num [cell13049]) (by norm_num [cell13049])
      exact ⟨E.1,E.2.trans (by norm_num [cell13049])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy32 (n := 13049) (by norm_num)
        (q := 1 - (cell13049 ⟨32,by decide⟩).lower)
        (by norm_num [cell13049]) (by norm_num [cell13049])
      exact ⟨E.1,E.2.trans (by norm_num [cell13049])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy33 (n := 13049) (by norm_num)
        (q := 1 - (cell13049 ⟨33,by decide⟩).lower)
        (by norm_num [cell13049]) (by norm_num [cell13049])
      exact ⟨E.1,E.2.trans (by norm_num [cell13049])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy34 (n := 13049) (by norm_num)
        (q := 1 - (cell13049 ⟨34,by decide⟩).lower)
        (by norm_num [cell13049]) (by norm_num [cell13049])
      exact ⟨E.1,E.2.trans (by norm_num [cell13049])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy35 (n := 13049) (by norm_num)
        (q := 1 - (cell13049 ⟨35,by decide⟩).lower)
        (by norm_num [cell13049]) (by norm_num [cell13049])
      exact ⟨E.1,E.2.trans (by norm_num [cell13049])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy36 (n := 13049) (by norm_num)
        (q := 1 - (cell13049 ⟨36,by decide⟩).lower)
        (by norm_num [cell13049]) (by norm_num [cell13049])
      exact ⟨E.1,E.2.trans (by norm_num [cell13049])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy37 (n := 13049) (by norm_num)
        (q := 1 - (cell13049 ⟨37,by decide⟩).lower)
        (by norm_num [cell13049]) (by norm_num [cell13049])
      exact ⟨E.1,E.2.trans (by norm_num [cell13049])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy38 (n := 13049) (by norm_num)
        (q := 1 - (cell13049 ⟨38,by decide⟩).lower)
        (by norm_num [cell13049]) (by norm_num [cell13049])
      exact ⟨E.1,E.2.trans (by norm_num [cell13049])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy39 (n := 13049) (by norm_num)
        (q := 1 - (cell13049 ⟨39,by decide⟩).lower)
        (by norm_num [cell13049]) (by norm_num [cell13049])
      exact ⟨E.1,E.2.trans (by norm_num [cell13049])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy40 (n := 13049) (by norm_num)
        (q := 1 - (cell13049 ⟨40,by decide⟩).lower)
        (by norm_num [cell13049]) (by norm_num [cell13049])
      exact ⟨E.1,E.2.trans (by norm_num [cell13049])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy41 (n := 13049) (by norm_num)
        (q := 1 - (cell13049 ⟨41,by decide⟩).lower)
        (by norm_num [cell13049]) (by norm_num [cell13049])
      exact ⟨E.1,E.2.trans (by norm_num [cell13049])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy42 (n := 13049) (by norm_num)
        (q := 1 - (cell13049 ⟨42,by decide⟩).lower)
        (by norm_num [cell13049]) (by norm_num [cell13049])
      exact ⟨E.1,E.2.trans (by norm_num [cell13049])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy43 (n := 13049) (by norm_num)
        (q := 1 - (cell13049 ⟨43,by decide⟩).lower)
        (by norm_num [cell13049]) (by norm_num [cell13049])
      exact ⟨E.1,E.2.trans (by norm_num [cell13049])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy44 (n := 13049) (by norm_num)
        (q := 1 - (cell13049 ⟨44,by decide⟩).lower)
        (by norm_num [cell13049]) (by norm_num [cell13049])
      exact ⟨E.1,E.2.trans (by norm_num [cell13049])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy45 (n := 13049) (by norm_num)
        (q := 1 - (cell13049 ⟨45,by decide⟩).lower)
        (by norm_num [cell13049]) (by norm_num [cell13049])
      exact ⟨E.1,E.2.trans (by norm_num [cell13049])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy46 (n := 13049) (by norm_num)
        (q := 1 - (cell13049 ⟨46,by decide⟩).lower)
        (by norm_num [cell13049]) (by norm_num [cell13049])
      exact ⟨E.1,E.2.trans (by norm_num [cell13049])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy47 (n := 13049) (by norm_num)
        (q := 1 - (cell13049 ⟨47,by decide⟩).lower)
        (by norm_num [cell13049]) (by norm_num [cell13049])
      exact ⟨E.1,E.2.trans (by norm_num [cell13049])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy48 (n := 13049) (by norm_num)
        (q := 1 - (cell13049 ⟨48,by decide⟩).lower)
        (by norm_num [cell13049]) (by norm_num [cell13049])
      exact ⟨E.1,E.2.trans (by norm_num [cell13049])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy49 (n := 13049) (by norm_num)
        (q := 1 - (cell13049 ⟨49,by decide⟩).lower)
        (by norm_num [cell13049]) (by norm_num [cell13049])
      exact ⟨E.1,E.2.trans (by norm_num [cell13049])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy50 (n := 13049) (by norm_num)
        (q := 1 - (cell13049 ⟨50,by decide⟩).lower)
        (by norm_num [cell13049]) (by norm_num [cell13049])
      exact ⟨E.1,E.2.trans (by norm_num [cell13049])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy51 (n := 13049) (by norm_num)
        (q := 1 - (cell13049 ⟨51,by decide⟩).lower)
        (by norm_num [cell13049]) (by norm_num [cell13049])
      exact ⟨E.1,E.2.trans (by norm_num [cell13049])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S27.uniformEnergy52 (n := 13049) (by norm_num)
        (q := 1 - (cell13049 ⟨52,by decide⟩).lower)
        (by norm_num [cell13049]) (by norm_num [cell13049])
      exact ⟨E.1,E.2.trans (by norm_num [cell13049])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13049

/-! Source-cell containment and simple scalar guards at 13049. -/
namespace BstLean.Part269.N13049
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13049)
open BstLean.Part268 (cell13049)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13049 ⟨10,by decide⟩).lower ∧ (cell13049 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13049 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13049 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13049 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13049 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13049 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13049,cell13049,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13049 ⟨11,by decide⟩).lower ∧ (cell13049 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13049 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13049 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13049 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13049 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13049 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13049,cell13049,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13049 ⟨12,by decide⟩).lower ∧ (cell13049 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13049 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13049 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13049 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13049 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13049 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13049,cell13049,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13049 ⟨13,by decide⟩).lower ∧ (cell13049 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13049 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13049 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13049 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13049 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13049 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13049,cell13049,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13049 ⟨14,by decide⟩).lower ∧ (cell13049 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13049 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13049 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13049 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13049 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13049 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13049,cell13049,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13049 ⟨15,by decide⟩).lower ∧ (cell13049 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13049 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13049 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13049 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13049 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13049 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13049,cell13049,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13049 ⟨16,by decide⟩).lower ∧ (cell13049 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13049 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13049 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13049 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13049 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13049 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13049,cell13049,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13049 ⟨17,by decide⟩).lower ∧ (cell13049 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13049 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13049 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13049 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13049 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13049 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13049,cell13049,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13049 ⟨18,by decide⟩).lower ∧ (cell13049 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13049 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13049 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13049 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13049 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13049 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13049,cell13049,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13049 ⟨19,by decide⟩).lower ∧ (cell13049 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13049 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13049 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13049 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13049 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13049 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13049,cell13049,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13049 ⟨20,by decide⟩).lower ∧ (cell13049 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13049 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13049 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13049 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13049 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13049 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13049,cell13049,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13049 ⟨21,by decide⟩).lower ∧ (cell13049 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13049 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13049 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13049 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13049 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13049 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13049,cell13049,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13049 ⟨22,by decide⟩).lower ∧ (cell13049 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13049 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13049 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13049 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13049 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13049 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13049,cell13049,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13049 ⟨23,by decide⟩).lower ∧ (cell13049 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13049 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13049 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13049 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13049 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13049 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13049,cell13049,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13049 ⟨24,by decide⟩).lower ∧ (cell13049 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13049 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13049 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13049 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13049 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13049 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13049,cell13049,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13049 ⟨25,by decide⟩).lower ∧ (cell13049 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13049 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13049 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13049 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13049 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13049 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13049,cell13049,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13049 ⟨26,by decide⟩).lower ∧ (cell13049 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13049 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13049 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13049 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13049 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13049 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13049,cell13049,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13049 ⟨27,by decide⟩).lower ∧ (cell13049 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13049 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13049 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13049 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13049 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13049 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13049,cell13049,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13049 ⟨28,by decide⟩).lower ∧ (cell13049 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13049 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13049 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13049 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13049 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13049 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13049,cell13049,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13049 ⟨29,by decide⟩).lower ∧ (cell13049 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13049 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13049 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13049 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13049 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13049 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13049,cell13049,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13049 ⟨30,by decide⟩).lower ∧ (cell13049 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13049 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13049 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13049 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13049 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13049 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13049,cell13049,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13049 ⟨31,by decide⟩).lower ∧ (cell13049 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13049 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13049 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13049 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13049 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13049 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13049,cell13049,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13049 ⟨32,by decide⟩).lower ∧ (cell13049 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13049 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13049 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13049 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13049 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13049 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13049,cell13049,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13049 ⟨33,by decide⟩).lower ∧ (cell13049 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13049 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13049 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13049 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13049 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13049 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13049,cell13049,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13049 ⟨34,by decide⟩).lower ∧ (cell13049 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13049 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13049 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13049 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13049 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13049 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13049,cell13049,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13049 ⟨35,by decide⟩).lower ∧ (cell13049 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13049 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13049 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13049 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13049 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13049 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13049,cell13049,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13049 ⟨36,by decide⟩).lower ∧ (cell13049 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13049 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13049 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13049 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13049 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13049 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13049,cell13049,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13049 ⟨37,by decide⟩).lower ∧ (cell13049 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13049 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13049 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13049 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13049 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13049 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13049,cell13049,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13049 ⟨38,by decide⟩).lower ∧ (cell13049 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13049 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13049 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13049 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13049 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13049 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13049,cell13049,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13049 ⟨39,by decide⟩).lower ∧ (cell13049 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13049 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13049 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13049 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13049 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13049 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13049,cell13049,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13049 ⟨40,by decide⟩).lower ∧ (cell13049 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13049 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13049 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13049 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13049 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13049 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13049,cell13049,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13049 ⟨41,by decide⟩).lower ∧ (cell13049 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13049 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13049 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13049 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13049 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13049 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13049,cell13049,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13049 ⟨42,by decide⟩).lower ∧ (cell13049 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13049 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13049 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13049 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13049 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13049 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13049,cell13049,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13049 ⟨43,by decide⟩).lower ∧ (cell13049 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13049 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13049 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13049 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13049 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13049 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13049,cell13049,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13049 ⟨44,by decide⟩).lower ∧ (cell13049 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13049 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13049 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13049 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13049 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13049 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13049,cell13049,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13049 ⟨45,by decide⟩).lower ∧ (cell13049 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13049 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13049 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13049 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13049 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13049 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13049,cell13049,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13049 ⟨46,by decide⟩).lower ∧ (cell13049 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13049 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13049 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13049 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13049 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13049 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13049,cell13049,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13049 ⟨47,by decide⟩).lower ∧ (cell13049 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13049 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13049 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13049 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13049 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13049 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13049,cell13049,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13049 ⟨48,by decide⟩).lower ∧ (cell13049 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13049 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13049 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13049 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13049 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13049 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13049,cell13049,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13049 ⟨49,by decide⟩).lower ∧ (cell13049 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13049 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13049 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13049 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13049 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13049 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13049,cell13049,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13049 ⟨50,by decide⟩).lower ∧ (cell13049 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13049 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13049 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13049 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13049 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13049 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13049,cell13049,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13049 ⟨51,by decide⟩).lower ∧ (cell13049 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13049 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13049 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13049 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13049 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13049 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13049,cell13049,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13049 ⟨52,by decide⟩).lower ∧ (cell13049 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13049 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13049 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13049 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13049 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13049 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13049,cell13049,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13049 i).lower ∧
    (cell13049 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13049 i).upper ≤ (0.532 : ℝ) ∧
    (cell13049 i).centre ≤ (0.1 : ℝ) ∧ (cell13049 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13049 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13049 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13049

/-! The local source numeric instances at 13049 have no network premises. -/
namespace BstLean.Part269.N13049
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13049)
open BstLean.Part268 (cell13049)

noncomputable def sourceNumerics13049 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13049 (cell13049 i)
      scalarRow13049.M scalarRow13049.H scalarRow13049.xi := by
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
    energy_allowance := scalarRow13049.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13049]
    centre_nonneg := (scalarRow13049.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D27.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13049])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13049