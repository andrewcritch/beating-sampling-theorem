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
import BstLean.Part269Direction6
import BstLean.Part269Shared6
import BstLean.Part269Finite
import BstLean.Part269Rows6
import BstLean.Part269Source
/-! Actual 12513 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12513
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12513 ≤ (1.036078165599 : ℝ) := by
  have hr : (111.861521534440 : ℝ) ≤ √(12513 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.861521534440 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12513 12513 (11 / 1000) ≤
    (0.008545271608 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12513) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.861521534440 : ℝ) ≤ √(12513 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12513)
  have hdiv : K / √(12513 : ℝ) ≤ K / 111.861521534440 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.861521534440 ≤ (0.008545271608 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12513.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12513 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12513 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12513 := gPlus_lower 12513
end BstLean.Part269.N12513

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12513
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036078165598 : ℝ) ≤ wn 12513 := by
  have hn : √(12513 : ℝ) ≤ 111.861521534441 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12513 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.861521534441 ≤ 2 / √(12513 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000255711469 : ℝ) ≤ rhoBar 12513 BstLean.Part154.csC ∧
    rhoBar 12513 BstLean.Part154.csC ≤ 0.000255711865 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036078165598 : ℝ) / (1.295212 * 12513) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036078165599 : ℝ) / (1.29521 * 12513) := by gcongr
      _ ≤ (0.000255711865 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12513 BstLean.Part154.csC) ≤ 0.001022912849 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12513 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12513 BstLean.Part154.csC) (piBar (rhoBar 12513 BstLean.Part154.csC)) ≤ 0.000195314586 ∧
    cc1 (rhoBar 12513 BstLean.Part154.csC) (piBar (rhoBar 12513 BstLean.Part154.csC)) ≤ 0.000124279939 ∧
    cc2 (rhoBar 12513 BstLean.Part154.csC) ≤ 0.000072145422 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12513 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12513 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12513 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12513 BstLean.Part154.csC * nuR (rhoBar 12513 BstLean.Part154.csC)) ≤ 0.000511440077 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000255711865 : ℝ) * 0.001022912849 := by gcongr
      _ ≤ (0.000511440077 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12513 BstLean.Part154.csC) * nuR (rhoBar 12513 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001022912849 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12513 BstLean.Part154.csC) * rhoBar 12513 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000255711865 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000255711865 / 2 + 0.399 * 0.001022912849 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000195314586 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000511440077 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124279939 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000255711865 / 1.414213562 := by gcongr
      _ ≤ (0.000072145422 : ℝ) := by norm_num

end BstLean.Part269.N12513

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12513
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12513 BstLean.Part154.csC) (piBar (rhoBar 12513 BstLean.Part154.csC)) ≤ 1.64742E-7 := by
  have hr0 : 0 ≤ rhoBar 12513 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12513 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12513 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12513 BstLean.Part154.csC) (piBar (rhoBar 12513 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12513 BstLean.Part154.csC) (piBar (rhoBar 12513 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12513 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000195314586 : ℝ) ^ 2 + 0.000124279939 ^ 2 + 3 * 0.000072145422 ^ 2 +
        2 * 0.797885 * 0.000195314586 * 0.000124279939 + 2 * 0.000195314586 * 0.000072145422 +
        4 * 0.797885 * 0.000124279939 * 0.000072145422 := by gcongr
    _ ≤ (1.64742E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12513 BstLean.Part154.csC Θ ≤ 0.002669971587 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12513 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12513 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12513 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12513 BstLean.Part154.csC) (piBar (rhoBar 12513 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12513 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036078165599 * 1.64742E-7 / (0.000255711469 : ℝ) := by gcongr
    _ ≤ 0.002669971587 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12513 BstLean.Part154.csC Θ ≤ 0.002963245868 + 0.000674657894 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12513 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12513 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12513 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036078165599 : ℝ) * ((2 * Θ * 0.000255711865 +
        (6863 / 10000) * 0.000255711865 * 12513 * 0.001022912849) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002963245868 + 0.000674657894 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12513 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12513 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12513 0.011 Θ ∧ gammaRatio 12513 0.011 Θ ≤ 0.000087907127 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12513 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036078165599 : ℝ) * 0.525 / ((1 - 0.011) * 12513) := by gcongr
      _ ≤ (0.000087907127 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12513 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12513 0.011 Θ) :=
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
    badAllowance 12513 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000774418828 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12513 BstLean.Part154.csC) 1.22 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 2 (rhoBar 12513 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12513 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12513 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12513 0.011 Θ) 1.12 ≤ 3.3895E-8 := by
    have he : (17.2 : ℝ) ≤ gap 1 (gammaRatio 12513 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12513 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12513 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12513 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12513 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036078165599 : ℝ) * 12513 *
        (2.7751E-8 / 1.1045361 + 3.3895E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000774418828 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12513 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003737664696 + 0.003344629481 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12513

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12513
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12513 BstLean.Part154.csC) (piBar (rhoBar 12513 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12513 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12513 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12513 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12513 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12513 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12513 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12513 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12513 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12513 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12513 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12513 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12513 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12513 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12513 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052879301537 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12513) ≤ 0.010676035555 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12513 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036078165599)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010676035555 + 2 * 0.737676 / 12513) := by gcongr
    _ ≤ (0.052879301537 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12513 12 ≤ 0.0015 := by
  exact BstLean.Part269.S6.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12513

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12513
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560494985215 : ℝ) ≤ plow 12513 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12513) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053000195174)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001401735084) : eMP 12513 0.011 xi bn ≤ 0.001206505705 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12513 : ℝ) * (1 - 0.011))) ≤ 0.000596525570 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001401735084 / (12513 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000596525570 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000596525570 : ℝ) + 3.141593 * 0.053000195174 / (12513 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001206505705 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053000195174)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001401735084) : PiBarMP 12513 12 0.011 xi bn ≤ 0.162463871911 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12513 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037439752724 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.244581890535 : ℝ) ≤ √((12513 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.861521534440 : ℝ) ≤ √(12513 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12513) ≤ 0.124550498435 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037439752724 + 0.053000195174 * 1.772454 / (2 * (111.244581890535 : ℝ))) * (1 + 0.001206505705) +
        8 / (12513 * 111.861521534440) + 0.124550498435 := by gcongr
    _ ≤ (0.162463871911 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053000195174)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001401735084) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283097014092) :
    parallelOracle 12513 0.011 xi bn cd ≤ 0.163469783701 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12513 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12513 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560494985215 : ℝ) ≤ plow 12513 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.861521534440 : ℝ) ≤ √(12513 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.283097014092 : ℝ) / (2 * 0.560494985215 * 111.861521534440)) * 0.162463871911 +
        0.283097014092 ^ 2 / (2 * 0.560494985215 * 111.861521534440) := by gcongr
    _ ≤ (0.163469783701 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053000195174) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001401735084)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283097014092) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12513 12513 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560494985215 : ℝ) ≤ plow 12513 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.861521534440 : ℝ) ≤ √(12513 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12513 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12513 Θ 1.22 ≤ 0.011854840537 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.861521534440 := by gcongr <;> linarith
      _ ≤ (0.011854840537 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12513 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12513 12513 0.011 ≤ 0.008545271608 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12513 12513 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12513 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12513 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12513 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12513 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163469783701 + 0.011854840537 + (0.008545271608 : ℝ) *
        (1 + 2 * (0.283097014092 + 0.011854840537) / (0.560494985215 * 111.861521534440))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12513]

end BstLean.Part269.N12513

/-! The original eight local profiles supply actual 12513 moment certificates. -/
namespace BstLean.Part269.N12513
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12513 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12513 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12513 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053000195174 ∧
    0 ≤ bN 12513 BstLean.Part154.csC (groupTheta g) ∧ bN 12513 BstLean.Part154.csC (groupTheta g) ≤ 0.001401735084 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12513 12513 0.011
      (momentAllowance 12513 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12513 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12513 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12513 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12513 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12513 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230217712555 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12513 0.011
      (momentAllowance 12513 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12513 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12513
/-! The actual computed-centre upper energy formula at 12513. -/
namespace BstLean.Part269.N12513
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12513

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12513
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12513)
open BstLean.Part268 (cell12513)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086055828030
  | 2 => 0.087009441467
  | 3 => 0.087962854487
  | 4 => 0.088917861833
  | 5 => 0.089876620917
  | 6 => 0.090841703904
  | 7 => 0.091816154386
  | 8 => 0.092803548612
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12513 12513 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12513 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003740909217 + 0.003348232271 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S6.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12513

/-! Actual upper energy certificates on all 43 source endpoints at 12513. -/
namespace BstLean.Part269.N12513
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12513)
open BstLean.Part268 (cell12513)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12513 (gMinus 12513) (1 - (cell12513 i).lower) ≤ 1 ∧
    energyUpper 12513 (gMinus 12513) (BstLean.Part211.gPlus 12513)
      (finiteEnergy 12513 12513 0.011) (1 - (cell12513 i).lower) ≤
      (cell12513 i).energy := by
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
      have E := BstLean.Part269.S6.uniformEnergy10 (n := 12513) (by norm_num)
        (q := 1 - (cell12513 ⟨10,by decide⟩).lower)
        (by norm_num [cell12513]) (by norm_num [cell12513])
      exact ⟨E.1,E.2.trans (by norm_num [cell12513])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy11 (n := 12513) (by norm_num)
        (q := 1 - (cell12513 ⟨11,by decide⟩).lower)
        (by norm_num [cell12513]) (by norm_num [cell12513])
      exact ⟨E.1,E.2.trans (by norm_num [cell12513])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy12 (n := 12513) (by norm_num)
        (q := 1 - (cell12513 ⟨12,by decide⟩).lower)
        (by norm_num [cell12513]) (by norm_num [cell12513])
      exact ⟨E.1,E.2.trans (by norm_num [cell12513])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy13 (n := 12513) (by norm_num)
        (q := 1 - (cell12513 ⟨13,by decide⟩).lower)
        (by norm_num [cell12513]) (by norm_num [cell12513])
      exact ⟨E.1,E.2.trans (by norm_num [cell12513])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy14 (n := 12513) (by norm_num)
        (q := 1 - (cell12513 ⟨14,by decide⟩).lower)
        (by norm_num [cell12513]) (by norm_num [cell12513])
      exact ⟨E.1,E.2.trans (by norm_num [cell12513])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy15 (n := 12513) (by norm_num)
        (q := 1 - (cell12513 ⟨15,by decide⟩).lower)
        (by norm_num [cell12513]) (by norm_num [cell12513])
      exact ⟨E.1,E.2.trans (by norm_num [cell12513])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy16 (n := 12513) (by norm_num)
        (q := 1 - (cell12513 ⟨16,by decide⟩).lower)
        (by norm_num [cell12513]) (by norm_num [cell12513])
      exact ⟨E.1,E.2.trans (by norm_num [cell12513])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy17 (n := 12513) (by norm_num)
        (q := 1 - (cell12513 ⟨17,by decide⟩).lower)
        (by norm_num [cell12513]) (by norm_num [cell12513])
      exact ⟨E.1,E.2.trans (by norm_num [cell12513])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy18 (n := 12513) (by norm_num)
        (q := 1 - (cell12513 ⟨18,by decide⟩).lower)
        (by norm_num [cell12513]) (by norm_num [cell12513])
      exact ⟨E.1,E.2.trans (by norm_num [cell12513])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy19 (n := 12513) (by norm_num)
        (q := 1 - (cell12513 ⟨19,by decide⟩).lower)
        (by norm_num [cell12513]) (by norm_num [cell12513])
      exact ⟨E.1,E.2.trans (by norm_num [cell12513])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy20 (n := 12513) (by norm_num)
        (q := 1 - (cell12513 ⟨20,by decide⟩).lower)
        (by norm_num [cell12513]) (by norm_num [cell12513])
      exact ⟨E.1,E.2.trans (by norm_num [cell12513])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy21 (n := 12513) (by norm_num)
        (q := 1 - (cell12513 ⟨21,by decide⟩).lower)
        (by norm_num [cell12513]) (by norm_num [cell12513])
      exact ⟨E.1,E.2.trans (by norm_num [cell12513])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy22 (n := 12513) (by norm_num)
        (q := 1 - (cell12513 ⟨22,by decide⟩).lower)
        (by norm_num [cell12513]) (by norm_num [cell12513])
      exact ⟨E.1,E.2.trans (by norm_num [cell12513])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy23 (n := 12513) (by norm_num)
        (q := 1 - (cell12513 ⟨23,by decide⟩).lower)
        (by norm_num [cell12513]) (by norm_num [cell12513])
      exact ⟨E.1,E.2.trans (by norm_num [cell12513])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy24 (n := 12513) (by norm_num)
        (q := 1 - (cell12513 ⟨24,by decide⟩).lower)
        (by norm_num [cell12513]) (by norm_num [cell12513])
      exact ⟨E.1,E.2.trans (by norm_num [cell12513])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy25 (n := 12513) (by norm_num)
        (q := 1 - (cell12513 ⟨25,by decide⟩).lower)
        (by norm_num [cell12513]) (by norm_num [cell12513])
      exact ⟨E.1,E.2.trans (by norm_num [cell12513])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy26 (n := 12513) (by norm_num)
        (q := 1 - (cell12513 ⟨26,by decide⟩).lower)
        (by norm_num [cell12513]) (by norm_num [cell12513])
      exact ⟨E.1,E.2.trans (by norm_num [cell12513])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy27 (n := 12513) (by norm_num)
        (q := 1 - (cell12513 ⟨27,by decide⟩).lower)
        (by norm_num [cell12513]) (by norm_num [cell12513])
      exact ⟨E.1,E.2.trans (by norm_num [cell12513])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy28 (n := 12513) (by norm_num)
        (q := 1 - (cell12513 ⟨28,by decide⟩).lower)
        (by norm_num [cell12513]) (by norm_num [cell12513])
      exact ⟨E.1,E.2.trans (by norm_num [cell12513])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy29 (n := 12513) (by norm_num)
        (q := 1 - (cell12513 ⟨29,by decide⟩).lower)
        (by norm_num [cell12513]) (by norm_num [cell12513])
      exact ⟨E.1,E.2.trans (by norm_num [cell12513])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy30 (n := 12513) (by norm_num)
        (q := 1 - (cell12513 ⟨30,by decide⟩).lower)
        (by norm_num [cell12513]) (by norm_num [cell12513])
      exact ⟨E.1,E.2.trans (by norm_num [cell12513])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy31 (n := 12513) (by norm_num)
        (q := 1 - (cell12513 ⟨31,by decide⟩).lower)
        (by norm_num [cell12513]) (by norm_num [cell12513])
      exact ⟨E.1,E.2.trans (by norm_num [cell12513])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy32 (n := 12513) (by norm_num)
        (q := 1 - (cell12513 ⟨32,by decide⟩).lower)
        (by norm_num [cell12513]) (by norm_num [cell12513])
      exact ⟨E.1,E.2.trans (by norm_num [cell12513])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy33 (n := 12513) (by norm_num)
        (q := 1 - (cell12513 ⟨33,by decide⟩).lower)
        (by norm_num [cell12513]) (by norm_num [cell12513])
      exact ⟨E.1,E.2.trans (by norm_num [cell12513])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy34 (n := 12513) (by norm_num)
        (q := 1 - (cell12513 ⟨34,by decide⟩).lower)
        (by norm_num [cell12513]) (by norm_num [cell12513])
      exact ⟨E.1,E.2.trans (by norm_num [cell12513])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy35 (n := 12513) (by norm_num)
        (q := 1 - (cell12513 ⟨35,by decide⟩).lower)
        (by norm_num [cell12513]) (by norm_num [cell12513])
      exact ⟨E.1,E.2.trans (by norm_num [cell12513])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy36 (n := 12513) (by norm_num)
        (q := 1 - (cell12513 ⟨36,by decide⟩).lower)
        (by norm_num [cell12513]) (by norm_num [cell12513])
      exact ⟨E.1,E.2.trans (by norm_num [cell12513])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy37 (n := 12513) (by norm_num)
        (q := 1 - (cell12513 ⟨37,by decide⟩).lower)
        (by norm_num [cell12513]) (by norm_num [cell12513])
      exact ⟨E.1,E.2.trans (by norm_num [cell12513])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy38 (n := 12513) (by norm_num)
        (q := 1 - (cell12513 ⟨38,by decide⟩).lower)
        (by norm_num [cell12513]) (by norm_num [cell12513])
      exact ⟨E.1,E.2.trans (by norm_num [cell12513])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy39 (n := 12513) (by norm_num)
        (q := 1 - (cell12513 ⟨39,by decide⟩).lower)
        (by norm_num [cell12513]) (by norm_num [cell12513])
      exact ⟨E.1,E.2.trans (by norm_num [cell12513])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy40 (n := 12513) (by norm_num)
        (q := 1 - (cell12513 ⟨40,by decide⟩).lower)
        (by norm_num [cell12513]) (by norm_num [cell12513])
      exact ⟨E.1,E.2.trans (by norm_num [cell12513])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy41 (n := 12513) (by norm_num)
        (q := 1 - (cell12513 ⟨41,by decide⟩).lower)
        (by norm_num [cell12513]) (by norm_num [cell12513])
      exact ⟨E.1,E.2.trans (by norm_num [cell12513])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy42 (n := 12513) (by norm_num)
        (q := 1 - (cell12513 ⟨42,by decide⟩).lower)
        (by norm_num [cell12513]) (by norm_num [cell12513])
      exact ⟨E.1,E.2.trans (by norm_num [cell12513])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy43 (n := 12513) (by norm_num)
        (q := 1 - (cell12513 ⟨43,by decide⟩).lower)
        (by norm_num [cell12513]) (by norm_num [cell12513])
      exact ⟨E.1,E.2.trans (by norm_num [cell12513])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy44 (n := 12513) (by norm_num)
        (q := 1 - (cell12513 ⟨44,by decide⟩).lower)
        (by norm_num [cell12513]) (by norm_num [cell12513])
      exact ⟨E.1,E.2.trans (by norm_num [cell12513])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy45 (n := 12513) (by norm_num)
        (q := 1 - (cell12513 ⟨45,by decide⟩).lower)
        (by norm_num [cell12513]) (by norm_num [cell12513])
      exact ⟨E.1,E.2.trans (by norm_num [cell12513])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy46 (n := 12513) (by norm_num)
        (q := 1 - (cell12513 ⟨46,by decide⟩).lower)
        (by norm_num [cell12513]) (by norm_num [cell12513])
      exact ⟨E.1,E.2.trans (by norm_num [cell12513])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy47 (n := 12513) (by norm_num)
        (q := 1 - (cell12513 ⟨47,by decide⟩).lower)
        (by norm_num [cell12513]) (by norm_num [cell12513])
      exact ⟨E.1,E.2.trans (by norm_num [cell12513])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy48 (n := 12513) (by norm_num)
        (q := 1 - (cell12513 ⟨48,by decide⟩).lower)
        (by norm_num [cell12513]) (by norm_num [cell12513])
      exact ⟨E.1,E.2.trans (by norm_num [cell12513])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy49 (n := 12513) (by norm_num)
        (q := 1 - (cell12513 ⟨49,by decide⟩).lower)
        (by norm_num [cell12513]) (by norm_num [cell12513])
      exact ⟨E.1,E.2.trans (by norm_num [cell12513])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy50 (n := 12513) (by norm_num)
        (q := 1 - (cell12513 ⟨50,by decide⟩).lower)
        (by norm_num [cell12513]) (by norm_num [cell12513])
      exact ⟨E.1,E.2.trans (by norm_num [cell12513])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy51 (n := 12513) (by norm_num)
        (q := 1 - (cell12513 ⟨51,by decide⟩).lower)
        (by norm_num [cell12513]) (by norm_num [cell12513])
      exact ⟨E.1,E.2.trans (by norm_num [cell12513])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy52 (n := 12513) (by norm_num)
        (q := 1 - (cell12513 ⟨52,by decide⟩).lower)
        (by norm_num [cell12513]) (by norm_num [cell12513])
      exact ⟨E.1,E.2.trans (by norm_num [cell12513])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12513

/-! Source-cell containment and simple scalar guards at 12513. -/
namespace BstLean.Part269.N12513
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12513)
open BstLean.Part268 (cell12513)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12513 ⟨10,by decide⟩).lower ∧ (cell12513 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12513 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12513 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12513 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12513 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12513 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12513,cell12513,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12513 ⟨11,by decide⟩).lower ∧ (cell12513 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12513 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12513 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12513 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12513 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12513 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12513,cell12513,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12513 ⟨12,by decide⟩).lower ∧ (cell12513 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12513 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12513 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12513 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12513 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12513 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12513,cell12513,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12513 ⟨13,by decide⟩).lower ∧ (cell12513 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12513 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12513 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12513 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12513 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12513 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12513,cell12513,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12513 ⟨14,by decide⟩).lower ∧ (cell12513 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12513 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12513 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12513 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12513 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12513 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12513,cell12513,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12513 ⟨15,by decide⟩).lower ∧ (cell12513 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12513 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12513 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12513 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12513 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12513 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12513,cell12513,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12513 ⟨16,by decide⟩).lower ∧ (cell12513 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12513 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12513 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12513 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12513 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12513 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12513,cell12513,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12513 ⟨17,by decide⟩).lower ∧ (cell12513 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12513 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12513 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12513 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12513 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12513 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12513,cell12513,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12513 ⟨18,by decide⟩).lower ∧ (cell12513 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12513 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12513 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12513 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12513 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12513 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12513,cell12513,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12513 ⟨19,by decide⟩).lower ∧ (cell12513 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12513 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12513 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12513 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12513 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12513 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12513,cell12513,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12513 ⟨20,by decide⟩).lower ∧ (cell12513 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12513 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12513 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12513 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12513 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12513 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12513,cell12513,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12513 ⟨21,by decide⟩).lower ∧ (cell12513 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12513 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12513 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12513 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12513 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12513 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12513,cell12513,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12513 ⟨22,by decide⟩).lower ∧ (cell12513 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12513 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12513 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12513 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12513 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12513 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12513,cell12513,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12513 ⟨23,by decide⟩).lower ∧ (cell12513 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12513 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12513 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12513 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12513 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12513 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12513,cell12513,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12513 ⟨24,by decide⟩).lower ∧ (cell12513 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12513 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12513 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12513 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12513 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12513 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12513,cell12513,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12513 ⟨25,by decide⟩).lower ∧ (cell12513 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12513 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12513 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12513 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12513 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12513 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12513,cell12513,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12513 ⟨26,by decide⟩).lower ∧ (cell12513 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12513 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12513 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12513 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12513 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12513 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12513,cell12513,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12513 ⟨27,by decide⟩).lower ∧ (cell12513 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12513 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12513 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12513 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12513 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12513 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12513,cell12513,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12513 ⟨28,by decide⟩).lower ∧ (cell12513 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12513 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12513 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12513 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12513 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12513 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12513,cell12513,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12513 ⟨29,by decide⟩).lower ∧ (cell12513 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12513 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12513 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12513 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12513 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12513 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12513,cell12513,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12513 ⟨30,by decide⟩).lower ∧ (cell12513 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12513 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12513 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12513 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12513 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12513 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12513,cell12513,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12513 ⟨31,by decide⟩).lower ∧ (cell12513 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12513 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12513 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12513 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12513 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12513 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12513,cell12513,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12513 ⟨32,by decide⟩).lower ∧ (cell12513 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12513 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12513 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12513 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12513 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12513 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12513,cell12513,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12513 ⟨33,by decide⟩).lower ∧ (cell12513 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12513 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12513 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12513 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12513 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12513 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12513,cell12513,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12513 ⟨34,by decide⟩).lower ∧ (cell12513 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12513 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12513 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12513 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12513 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12513 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12513,cell12513,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12513 ⟨35,by decide⟩).lower ∧ (cell12513 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12513 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12513 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12513 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12513 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12513 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12513,cell12513,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12513 ⟨36,by decide⟩).lower ∧ (cell12513 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12513 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12513 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12513 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12513 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12513 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12513,cell12513,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12513 ⟨37,by decide⟩).lower ∧ (cell12513 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12513 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12513 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12513 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12513 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12513 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12513,cell12513,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12513 ⟨38,by decide⟩).lower ∧ (cell12513 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12513 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12513 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12513 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12513 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12513 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12513,cell12513,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12513 ⟨39,by decide⟩).lower ∧ (cell12513 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12513 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12513 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12513 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12513 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12513 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12513,cell12513,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12513 ⟨40,by decide⟩).lower ∧ (cell12513 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12513 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12513 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12513 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12513 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12513 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12513,cell12513,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12513 ⟨41,by decide⟩).lower ∧ (cell12513 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12513 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12513 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12513 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12513 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12513 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12513,cell12513,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12513 ⟨42,by decide⟩).lower ∧ (cell12513 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12513 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12513 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12513 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12513 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12513 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12513,cell12513,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12513 ⟨43,by decide⟩).lower ∧ (cell12513 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12513 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12513 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12513 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12513 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12513 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12513,cell12513,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12513 ⟨44,by decide⟩).lower ∧ (cell12513 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12513 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12513 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12513 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12513 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12513 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12513,cell12513,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12513 ⟨45,by decide⟩).lower ∧ (cell12513 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12513 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12513 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12513 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12513 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12513 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12513,cell12513,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12513 ⟨46,by decide⟩).lower ∧ (cell12513 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12513 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12513 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12513 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12513 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12513 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12513,cell12513,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12513 ⟨47,by decide⟩).lower ∧ (cell12513 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12513 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12513 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12513 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12513 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12513 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12513,cell12513,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12513 ⟨48,by decide⟩).lower ∧ (cell12513 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12513 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12513 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12513 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12513 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12513 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12513,cell12513,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12513 ⟨49,by decide⟩).lower ∧ (cell12513 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12513 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12513 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12513 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12513 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12513 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12513,cell12513,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12513 ⟨50,by decide⟩).lower ∧ (cell12513 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12513 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12513 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12513 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12513 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12513 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12513,cell12513,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12513 ⟨51,by decide⟩).lower ∧ (cell12513 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12513 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12513 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12513 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12513 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12513 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12513,cell12513,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12513 ⟨52,by decide⟩).lower ∧ (cell12513 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12513 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12513 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12513 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12513 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12513 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12513,cell12513,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12513 i).lower ∧
    (cell12513 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12513 i).upper ≤ (0.532 : ℝ) ∧
    (cell12513 i).centre ≤ (0.1 : ℝ) ∧ (cell12513 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12513 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12513 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12513

/-! The local source numeric instances at 12513 have no network premises. -/
namespace BstLean.Part269.N12513
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12513)
open BstLean.Part268 (cell12513)

noncomputable def sourceNumerics12513 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12513 (cell12513 i)
      scalarRow12513.M scalarRow12513.H scalarRow12513.xi := by
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
    energy_allowance := scalarRow12513.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12513]
    centre_nonneg := (scalarRow12513.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D6.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12513])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12513
/-! Actual 12514 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12514
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12514 ≤ (1.036076711286 : ℝ) := by
  have hr : (111.865991257396 : ℝ) ≤ √(12514 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.865991257396 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12514 12514 (11 / 1000) ≤
    (0.008544930170 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12514) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.865991257396 : ℝ) ≤ √(12514 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12514)
  have hdiv : K / √(12514 : ℝ) ≤ K / 111.865991257396 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.865991257396 ≤ (0.008544930170 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12514.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12514 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12514 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12514 := gPlus_lower 12514
end BstLean.Part269.N12514

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12514
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036076711285 : ℝ) ≤ wn 12514 := by
  have hn : √(12514 : ℝ) ≤ 111.865991257397 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12514 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.865991257397 ≤ 2 / √(12514 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000255690677 : ℝ) ≤ rhoBar 12514 BstLean.Part154.csC ∧
    rhoBar 12514 BstLean.Part154.csC ≤ 0.000255691072 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036076711285 : ℝ) / (1.295212 * 12514) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036076711286 : ℝ) / (1.29521 * 12514) := by gcongr
      _ ≤ (0.000255691072 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12514 BstLean.Part154.csC) ≤ 0.001022829666 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12514 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12514 BstLean.Part154.csC) (piBar (rhoBar 12514 BstLean.Part154.csC)) ≤ 0.000195298703 ∧
    cc1 (rhoBar 12514 BstLean.Part154.csC) (piBar (rhoBar 12514 BstLean.Part154.csC)) ≤ 0.000124269833 ∧
    cc2 (rhoBar 12514 BstLean.Part154.csC) ≤ 0.000072139556 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12514 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12514 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12514 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12514 BstLean.Part154.csC * nuR (rhoBar 12514 BstLean.Part154.csC)) ≤ 0.000511398489 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000255691072 : ℝ) * 0.001022829666 := by gcongr
      _ ≤ (0.000511398489 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12514 BstLean.Part154.csC) * nuR (rhoBar 12514 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001022829666 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12514 BstLean.Part154.csC) * rhoBar 12514 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000255691072 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000255691072 / 2 + 0.399 * 0.001022829666 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000195298703 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000511398489 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124269833 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000255691072 / 1.414213562 := by gcongr
      _ ≤ (0.000072139556 : ℝ) := by norm_num

end BstLean.Part269.N12514

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12514
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12514 BstLean.Part154.csC) (piBar (rhoBar 12514 BstLean.Part154.csC)) ≤ 1.64715E-7 := by
  have hr0 : 0 ≤ rhoBar 12514 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12514 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12514 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12514 BstLean.Part154.csC) (piBar (rhoBar 12514 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12514 BstLean.Part154.csC) (piBar (rhoBar 12514 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12514 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000195298703 : ℝ) ^ 2 + 0.000124269833 ^ 2 + 3 * 0.000072139556 ^ 2 +
        2 * 0.797885 * 0.000195298703 * 0.000124269833 + 2 * 0.000195298703 * 0.000072139556 +
        4 * 0.797885 * 0.000124269833 * 0.000072139556 := by gcongr
    _ ≤ (1.64715E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12514 BstLean.Part154.csC Θ ≤ 0.002669747330 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12514 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12514 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12514 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12514 BstLean.Part154.csC) (piBar (rhoBar 12514 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12514 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036076711286 * 1.64715E-7 / (0.000255690677 : ℝ) := by gcongr
    _ ≤ 0.002669747330 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12514 BstLean.Part154.csC Θ ≤ 0.002962996580 + 0.000674602088 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12514 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12514 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12514 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036076711286 : ℝ) * ((2 * Θ * 0.000255691072 +
        (6863 / 10000) * 0.000255691072 * 12514 * 0.001022829666) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002962996580 + 0.000674602088 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12514 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12514 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12514 0.011 Θ ∧ gammaRatio 12514 0.011 Θ ≤ 0.000087899979 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12514 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036076711286 : ℝ) * 0.525 / ((1 - 0.011) * 12514) := by gcongr
      _ ≤ (0.000087899979 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12514 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12514 0.011 Θ) :=
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
    badAllowance 12514 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000774418828 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12514 BstLean.Part154.csC) 1.22 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 2 (rhoBar 12514 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12514 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12514 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12514 0.011 Θ) 1.12 ≤ 3.3895E-8 := by
    have he : (17.2 : ℝ) ≤ gap 1 (gammaRatio 12514 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12514 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12514 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12514 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12514 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036076711286 : ℝ) * 12514 *
        (2.7751E-8 / 1.1045361 + 3.3895E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000774418828 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12514 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003737415408 + 0.003344349418 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12514

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12514
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12514 BstLean.Part154.csC) (piBar (rhoBar 12514 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12514 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12514 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12514 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12514 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12514 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12514 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12514 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12514 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12514 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12514 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12514 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12514 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12514 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12514 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052877165612 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12514) ≤ 0.010675608983 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12514 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036076711286)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010675608983 + 2 * 0.737676 / 12514) := by gcongr
    _ ≤ (0.052877165612 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12514 12 ≤ 0.0015 := by
  exact BstLean.Part269.S6.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12514

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12514
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560495031796 : ℝ) ≤ plow 12514 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12514) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052999798853)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001401617349) : eMP 12514 0.011 xi bn ≤ 0.001206406757 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12514 : ℝ) * (1 - 0.011))) ≤ 0.000596476684 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001401617349 / (12514 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000596476684 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000596476684 : ℝ) + 3.141593 * 0.052999798853 / (12514 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001206406757 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052999798853)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001401617349) : PiBarMP 12514 12 0.011 xi bn ≤ 0.162457296626 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12514 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037438180365 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.249026962036 : ℝ) ≤ √((12514 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.865991257396 : ℝ) ≤ √(12514 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12514) ≤ 0.124545521889 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037438180365 + 0.052999798853 * 1.772454 / (2 * (111.249026962036 : ℝ))) * (1 + 0.001206406757) +
        8 / (12514 * 111.865991257396) + 0.124545521889 := by gcongr
    _ ≤ (0.162457296626 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052999798853)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001401617349) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283094017413) :
    parallelOracle 12514 0.011 xi bn cd ≤ 0.163463135884 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12514 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12514 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560495031796 : ℝ) ≤ plow 12514 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.865991257396 : ℝ) ≤ √(12514 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.283094017413 : ℝ) / (2 * 0.560495031796 * 111.865991257396)) * 0.162457296626 +
        0.283094017413 ^ 2 / (2 * 0.560495031796 * 111.865991257396) := by gcongr
    _ ≤ (0.163463135884 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052999798853) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001401617349)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283094017413) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12514 12514 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560495031796 : ℝ) ≤ plow 12514 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.865991257396 : ℝ) ≤ √(12514 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12514 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12514 Θ 1.22 ≤ 0.011854366865 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.865991257396 := by gcongr <;> linarith
      _ ≤ (0.011854366865 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12514 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12514 12514 0.011 ≤ 0.008544930170 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12514 12514 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12514 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12514 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12514 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12514 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163463135884 + 0.011854366865 + (0.008544930170 : ℝ) *
        (1 + 2 * (0.283094017413 + 0.011854366865) / (0.560495031796 * 111.865991257396))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12514]

end BstLean.Part269.N12514

/-! The original eight local profiles supply actual 12514 moment certificates. -/
namespace BstLean.Part269.N12514
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12514 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12514 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12514 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052999798853 ∧
    0 ≤ bN 12514 BstLean.Part154.csC (groupTheta g) ∧ bN 12514 BstLean.Part154.csC (groupTheta g) ≤ 0.001401617349 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12514 12514 0.011
      (momentAllowance 12514 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12514 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12514 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12514 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12514 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12514 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230216851801 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12514 0.011
      (momentAllowance 12514 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12514 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12514
/-! The actual computed-centre upper energy formula at 12514. -/
namespace BstLean.Part269.N12514
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12514

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12514
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12514)
open BstLean.Part268 (cell12514)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086052688854
  | 2 => 0.087006239321
  | 3 => 0.087959579352
  | 4 => 0.088914501449
  | 5 => 0.089873160395
  | 6 => 0.090838125299
  | 7 => 0.091812436217
  | 8 => 0.092799665336
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12514 12514 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12514 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003740909217 + 0.003348232271 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S6.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12514

/-! Actual upper energy certificates on all 43 source endpoints at 12514. -/
namespace BstLean.Part269.N12514
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12514)
open BstLean.Part268 (cell12514)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12514 (gMinus 12514) (1 - (cell12514 i).lower) ≤ 1 ∧
    energyUpper 12514 (gMinus 12514) (BstLean.Part211.gPlus 12514)
      (finiteEnergy 12514 12514 0.011) (1 - (cell12514 i).lower) ≤
      (cell12514 i).energy := by
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
      have E := BstLean.Part269.S6.uniformEnergy10 (n := 12514) (by norm_num)
        (q := 1 - (cell12514 ⟨10,by decide⟩).lower)
        (by norm_num [cell12514]) (by norm_num [cell12514])
      exact ⟨E.1,E.2.trans (by norm_num [cell12514])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy11 (n := 12514) (by norm_num)
        (q := 1 - (cell12514 ⟨11,by decide⟩).lower)
        (by norm_num [cell12514]) (by norm_num [cell12514])
      exact ⟨E.1,E.2.trans (by norm_num [cell12514])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy12 (n := 12514) (by norm_num)
        (q := 1 - (cell12514 ⟨12,by decide⟩).lower)
        (by norm_num [cell12514]) (by norm_num [cell12514])
      exact ⟨E.1,E.2.trans (by norm_num [cell12514])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy13 (n := 12514) (by norm_num)
        (q := 1 - (cell12514 ⟨13,by decide⟩).lower)
        (by norm_num [cell12514]) (by norm_num [cell12514])
      exact ⟨E.1,E.2.trans (by norm_num [cell12514])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy14 (n := 12514) (by norm_num)
        (q := 1 - (cell12514 ⟨14,by decide⟩).lower)
        (by norm_num [cell12514]) (by norm_num [cell12514])
      exact ⟨E.1,E.2.trans (by norm_num [cell12514])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy15 (n := 12514) (by norm_num)
        (q := 1 - (cell12514 ⟨15,by decide⟩).lower)
        (by norm_num [cell12514]) (by norm_num [cell12514])
      exact ⟨E.1,E.2.trans (by norm_num [cell12514])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy16 (n := 12514) (by norm_num)
        (q := 1 - (cell12514 ⟨16,by decide⟩).lower)
        (by norm_num [cell12514]) (by norm_num [cell12514])
      exact ⟨E.1,E.2.trans (by norm_num [cell12514])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy17 (n := 12514) (by norm_num)
        (q := 1 - (cell12514 ⟨17,by decide⟩).lower)
        (by norm_num [cell12514]) (by norm_num [cell12514])
      exact ⟨E.1,E.2.trans (by norm_num [cell12514])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy18 (n := 12514) (by norm_num)
        (q := 1 - (cell12514 ⟨18,by decide⟩).lower)
        (by norm_num [cell12514]) (by norm_num [cell12514])
      exact ⟨E.1,E.2.trans (by norm_num [cell12514])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy19 (n := 12514) (by norm_num)
        (q := 1 - (cell12514 ⟨19,by decide⟩).lower)
        (by norm_num [cell12514]) (by norm_num [cell12514])
      exact ⟨E.1,E.2.trans (by norm_num [cell12514])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy20 (n := 12514) (by norm_num)
        (q := 1 - (cell12514 ⟨20,by decide⟩).lower)
        (by norm_num [cell12514]) (by norm_num [cell12514])
      exact ⟨E.1,E.2.trans (by norm_num [cell12514])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy21 (n := 12514) (by norm_num)
        (q := 1 - (cell12514 ⟨21,by decide⟩).lower)
        (by norm_num [cell12514]) (by norm_num [cell12514])
      exact ⟨E.1,E.2.trans (by norm_num [cell12514])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy22 (n := 12514) (by norm_num)
        (q := 1 - (cell12514 ⟨22,by decide⟩).lower)
        (by norm_num [cell12514]) (by norm_num [cell12514])
      exact ⟨E.1,E.2.trans (by norm_num [cell12514])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy23 (n := 12514) (by norm_num)
        (q := 1 - (cell12514 ⟨23,by decide⟩).lower)
        (by norm_num [cell12514]) (by norm_num [cell12514])
      exact ⟨E.1,E.2.trans (by norm_num [cell12514])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy24 (n := 12514) (by norm_num)
        (q := 1 - (cell12514 ⟨24,by decide⟩).lower)
        (by norm_num [cell12514]) (by norm_num [cell12514])
      exact ⟨E.1,E.2.trans (by norm_num [cell12514])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy25 (n := 12514) (by norm_num)
        (q := 1 - (cell12514 ⟨25,by decide⟩).lower)
        (by norm_num [cell12514]) (by norm_num [cell12514])
      exact ⟨E.1,E.2.trans (by norm_num [cell12514])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy26 (n := 12514) (by norm_num)
        (q := 1 - (cell12514 ⟨26,by decide⟩).lower)
        (by norm_num [cell12514]) (by norm_num [cell12514])
      exact ⟨E.1,E.2.trans (by norm_num [cell12514])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy27 (n := 12514) (by norm_num)
        (q := 1 - (cell12514 ⟨27,by decide⟩).lower)
        (by norm_num [cell12514]) (by norm_num [cell12514])
      exact ⟨E.1,E.2.trans (by norm_num [cell12514])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy28 (n := 12514) (by norm_num)
        (q := 1 - (cell12514 ⟨28,by decide⟩).lower)
        (by norm_num [cell12514]) (by norm_num [cell12514])
      exact ⟨E.1,E.2.trans (by norm_num [cell12514])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy29 (n := 12514) (by norm_num)
        (q := 1 - (cell12514 ⟨29,by decide⟩).lower)
        (by norm_num [cell12514]) (by norm_num [cell12514])
      exact ⟨E.1,E.2.trans (by norm_num [cell12514])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy30 (n := 12514) (by norm_num)
        (q := 1 - (cell12514 ⟨30,by decide⟩).lower)
        (by norm_num [cell12514]) (by norm_num [cell12514])
      exact ⟨E.1,E.2.trans (by norm_num [cell12514])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy31 (n := 12514) (by norm_num)
        (q := 1 - (cell12514 ⟨31,by decide⟩).lower)
        (by norm_num [cell12514]) (by norm_num [cell12514])
      exact ⟨E.1,E.2.trans (by norm_num [cell12514])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy32 (n := 12514) (by norm_num)
        (q := 1 - (cell12514 ⟨32,by decide⟩).lower)
        (by norm_num [cell12514]) (by norm_num [cell12514])
      exact ⟨E.1,E.2.trans (by norm_num [cell12514])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy33 (n := 12514) (by norm_num)
        (q := 1 - (cell12514 ⟨33,by decide⟩).lower)
        (by norm_num [cell12514]) (by norm_num [cell12514])
      exact ⟨E.1,E.2.trans (by norm_num [cell12514])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy34 (n := 12514) (by norm_num)
        (q := 1 - (cell12514 ⟨34,by decide⟩).lower)
        (by norm_num [cell12514]) (by norm_num [cell12514])
      exact ⟨E.1,E.2.trans (by norm_num [cell12514])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy35 (n := 12514) (by norm_num)
        (q := 1 - (cell12514 ⟨35,by decide⟩).lower)
        (by norm_num [cell12514]) (by norm_num [cell12514])
      exact ⟨E.1,E.2.trans (by norm_num [cell12514])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy36 (n := 12514) (by norm_num)
        (q := 1 - (cell12514 ⟨36,by decide⟩).lower)
        (by norm_num [cell12514]) (by norm_num [cell12514])
      exact ⟨E.1,E.2.trans (by norm_num [cell12514])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy37 (n := 12514) (by norm_num)
        (q := 1 - (cell12514 ⟨37,by decide⟩).lower)
        (by norm_num [cell12514]) (by norm_num [cell12514])
      exact ⟨E.1,E.2.trans (by norm_num [cell12514])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy38 (n := 12514) (by norm_num)
        (q := 1 - (cell12514 ⟨38,by decide⟩).lower)
        (by norm_num [cell12514]) (by norm_num [cell12514])
      exact ⟨E.1,E.2.trans (by norm_num [cell12514])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy39 (n := 12514) (by norm_num)
        (q := 1 - (cell12514 ⟨39,by decide⟩).lower)
        (by norm_num [cell12514]) (by norm_num [cell12514])
      exact ⟨E.1,E.2.trans (by norm_num [cell12514])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy40 (n := 12514) (by norm_num)
        (q := 1 - (cell12514 ⟨40,by decide⟩).lower)
        (by norm_num [cell12514]) (by norm_num [cell12514])
      exact ⟨E.1,E.2.trans (by norm_num [cell12514])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy41 (n := 12514) (by norm_num)
        (q := 1 - (cell12514 ⟨41,by decide⟩).lower)
        (by norm_num [cell12514]) (by norm_num [cell12514])
      exact ⟨E.1,E.2.trans (by norm_num [cell12514])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy42 (n := 12514) (by norm_num)
        (q := 1 - (cell12514 ⟨42,by decide⟩).lower)
        (by norm_num [cell12514]) (by norm_num [cell12514])
      exact ⟨E.1,E.2.trans (by norm_num [cell12514])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy43 (n := 12514) (by norm_num)
        (q := 1 - (cell12514 ⟨43,by decide⟩).lower)
        (by norm_num [cell12514]) (by norm_num [cell12514])
      exact ⟨E.1,E.2.trans (by norm_num [cell12514])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy44 (n := 12514) (by norm_num)
        (q := 1 - (cell12514 ⟨44,by decide⟩).lower)
        (by norm_num [cell12514]) (by norm_num [cell12514])
      exact ⟨E.1,E.2.trans (by norm_num [cell12514])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy45 (n := 12514) (by norm_num)
        (q := 1 - (cell12514 ⟨45,by decide⟩).lower)
        (by norm_num [cell12514]) (by norm_num [cell12514])
      exact ⟨E.1,E.2.trans (by norm_num [cell12514])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy46 (n := 12514) (by norm_num)
        (q := 1 - (cell12514 ⟨46,by decide⟩).lower)
        (by norm_num [cell12514]) (by norm_num [cell12514])
      exact ⟨E.1,E.2.trans (by norm_num [cell12514])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy47 (n := 12514) (by norm_num)
        (q := 1 - (cell12514 ⟨47,by decide⟩).lower)
        (by norm_num [cell12514]) (by norm_num [cell12514])
      exact ⟨E.1,E.2.trans (by norm_num [cell12514])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy48 (n := 12514) (by norm_num)
        (q := 1 - (cell12514 ⟨48,by decide⟩).lower)
        (by norm_num [cell12514]) (by norm_num [cell12514])
      exact ⟨E.1,E.2.trans (by norm_num [cell12514])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy49 (n := 12514) (by norm_num)
        (q := 1 - (cell12514 ⟨49,by decide⟩).lower)
        (by norm_num [cell12514]) (by norm_num [cell12514])
      exact ⟨E.1,E.2.trans (by norm_num [cell12514])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy50 (n := 12514) (by norm_num)
        (q := 1 - (cell12514 ⟨50,by decide⟩).lower)
        (by norm_num [cell12514]) (by norm_num [cell12514])
      exact ⟨E.1,E.2.trans (by norm_num [cell12514])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy51 (n := 12514) (by norm_num)
        (q := 1 - (cell12514 ⟨51,by decide⟩).lower)
        (by norm_num [cell12514]) (by norm_num [cell12514])
      exact ⟨E.1,E.2.trans (by norm_num [cell12514])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy52 (n := 12514) (by norm_num)
        (q := 1 - (cell12514 ⟨52,by decide⟩).lower)
        (by norm_num [cell12514]) (by norm_num [cell12514])
      exact ⟨E.1,E.2.trans (by norm_num [cell12514])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12514

/-! Source-cell containment and simple scalar guards at 12514. -/
namespace BstLean.Part269.N12514
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12514)
open BstLean.Part268 (cell12514)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12514 ⟨10,by decide⟩).lower ∧ (cell12514 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12514 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12514 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12514 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12514 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12514 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12514,cell12514,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12514 ⟨11,by decide⟩).lower ∧ (cell12514 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12514 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12514 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12514 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12514 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12514 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12514,cell12514,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12514 ⟨12,by decide⟩).lower ∧ (cell12514 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12514 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12514 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12514 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12514 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12514 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12514,cell12514,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12514 ⟨13,by decide⟩).lower ∧ (cell12514 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12514 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12514 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12514 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12514 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12514 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12514,cell12514,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12514 ⟨14,by decide⟩).lower ∧ (cell12514 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12514 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12514 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12514 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12514 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12514 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12514,cell12514,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12514 ⟨15,by decide⟩).lower ∧ (cell12514 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12514 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12514 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12514 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12514 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12514 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12514,cell12514,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12514 ⟨16,by decide⟩).lower ∧ (cell12514 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12514 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12514 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12514 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12514 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12514 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12514,cell12514,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12514 ⟨17,by decide⟩).lower ∧ (cell12514 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12514 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12514 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12514 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12514 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12514 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12514,cell12514,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12514 ⟨18,by decide⟩).lower ∧ (cell12514 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12514 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12514 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12514 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12514 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12514 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12514,cell12514,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12514 ⟨19,by decide⟩).lower ∧ (cell12514 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12514 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12514 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12514 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12514 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12514 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12514,cell12514,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12514 ⟨20,by decide⟩).lower ∧ (cell12514 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12514 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12514 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12514 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12514 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12514 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12514,cell12514,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12514 ⟨21,by decide⟩).lower ∧ (cell12514 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12514 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12514 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12514 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12514 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12514 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12514,cell12514,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12514 ⟨22,by decide⟩).lower ∧ (cell12514 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12514 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12514 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12514 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12514 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12514 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12514,cell12514,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12514 ⟨23,by decide⟩).lower ∧ (cell12514 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12514 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12514 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12514 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12514 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12514 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12514,cell12514,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12514 ⟨24,by decide⟩).lower ∧ (cell12514 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12514 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12514 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12514 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12514 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12514 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12514,cell12514,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12514 ⟨25,by decide⟩).lower ∧ (cell12514 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12514 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12514 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12514 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12514 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12514 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12514,cell12514,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12514 ⟨26,by decide⟩).lower ∧ (cell12514 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12514 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12514 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12514 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12514 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12514 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12514,cell12514,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12514 ⟨27,by decide⟩).lower ∧ (cell12514 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12514 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12514 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12514 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12514 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12514 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12514,cell12514,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12514 ⟨28,by decide⟩).lower ∧ (cell12514 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12514 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12514 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12514 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12514 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12514 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12514,cell12514,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12514 ⟨29,by decide⟩).lower ∧ (cell12514 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12514 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12514 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12514 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12514 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12514 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12514,cell12514,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12514 ⟨30,by decide⟩).lower ∧ (cell12514 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12514 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12514 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12514 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12514 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12514 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12514,cell12514,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12514 ⟨31,by decide⟩).lower ∧ (cell12514 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12514 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12514 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12514 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12514 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12514 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12514,cell12514,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12514 ⟨32,by decide⟩).lower ∧ (cell12514 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12514 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12514 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12514 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12514 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12514 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12514,cell12514,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12514 ⟨33,by decide⟩).lower ∧ (cell12514 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12514 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12514 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12514 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12514 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12514 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12514,cell12514,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12514 ⟨34,by decide⟩).lower ∧ (cell12514 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12514 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12514 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12514 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12514 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12514 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12514,cell12514,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12514 ⟨35,by decide⟩).lower ∧ (cell12514 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12514 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12514 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12514 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12514 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12514 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12514,cell12514,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12514 ⟨36,by decide⟩).lower ∧ (cell12514 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12514 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12514 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12514 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12514 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12514 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12514,cell12514,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12514 ⟨37,by decide⟩).lower ∧ (cell12514 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12514 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12514 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12514 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12514 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12514 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12514,cell12514,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12514 ⟨38,by decide⟩).lower ∧ (cell12514 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12514 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12514 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12514 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12514 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12514 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12514,cell12514,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12514 ⟨39,by decide⟩).lower ∧ (cell12514 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12514 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12514 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12514 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12514 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12514 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12514,cell12514,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12514 ⟨40,by decide⟩).lower ∧ (cell12514 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12514 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12514 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12514 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12514 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12514 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12514,cell12514,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12514 ⟨41,by decide⟩).lower ∧ (cell12514 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12514 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12514 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12514 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12514 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12514 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12514,cell12514,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12514 ⟨42,by decide⟩).lower ∧ (cell12514 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12514 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12514 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12514 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12514 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12514 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12514,cell12514,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12514 ⟨43,by decide⟩).lower ∧ (cell12514 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12514 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12514 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12514 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12514 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12514 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12514,cell12514,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12514 ⟨44,by decide⟩).lower ∧ (cell12514 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12514 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12514 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12514 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12514 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12514 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12514,cell12514,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12514 ⟨45,by decide⟩).lower ∧ (cell12514 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12514 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12514 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12514 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12514 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12514 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12514,cell12514,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12514 ⟨46,by decide⟩).lower ∧ (cell12514 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12514 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12514 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12514 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12514 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12514 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12514,cell12514,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12514 ⟨47,by decide⟩).lower ∧ (cell12514 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12514 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12514 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12514 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12514 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12514 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12514,cell12514,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12514 ⟨48,by decide⟩).lower ∧ (cell12514 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12514 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12514 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12514 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12514 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12514 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12514,cell12514,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12514 ⟨49,by decide⟩).lower ∧ (cell12514 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12514 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12514 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12514 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12514 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12514 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12514,cell12514,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12514 ⟨50,by decide⟩).lower ∧ (cell12514 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12514 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12514 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12514 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12514 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12514 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12514,cell12514,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12514 ⟨51,by decide⟩).lower ∧ (cell12514 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12514 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12514 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12514 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12514 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12514 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12514,cell12514,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12514 ⟨52,by decide⟩).lower ∧ (cell12514 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12514 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12514 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12514 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12514 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12514 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12514,cell12514,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12514 i).lower ∧
    (cell12514 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12514 i).upper ≤ (0.532 : ℝ) ∧
    (cell12514 i).centre ≤ (0.1 : ℝ) ∧ (cell12514 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12514 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12514 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12514

/-! The local source numeric instances at 12514 have no network premises. -/
namespace BstLean.Part269.N12514
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12514)
open BstLean.Part268 (cell12514)

noncomputable def sourceNumerics12514 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12514 (cell12514 i)
      scalarRow12514.M scalarRow12514.H scalarRow12514.xi := by
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
    energy_allowance := scalarRow12514.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12514]
    centre_nonneg := (scalarRow12514.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D6.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12514])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12514
/-! Actual 12515 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12515
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12515 ≤ (1.036075257148 : ℝ) := by
  have hr : (111.870460801768 : ℝ) ≤ √(12515 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.870460801768 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12515 12515 (11 / 1000) ≤
    (0.008544588773 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12515) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.870460801768 : ℝ) ≤ √(12515 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12515)
  have hdiv : K / √(12515 : ℝ) ≤ K / 111.870460801768 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.870460801768 ≤ (0.008544588773 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12515.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12515 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12515 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12515 := gPlus_lower 12515
end BstLean.Part269.N12515

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12515
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036075257147 : ℝ) ≤ wn 12515 := by
  have hn : √(12515 : ℝ) ≤ 111.870460801769 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12515 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.870460801769 ≤ 2 / √(12515 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000255669887 : ℝ) ≤ rhoBar 12515 BstLean.Part154.csC ∧
    rhoBar 12515 BstLean.Part154.csC ≤ 0.000255670283 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036075257147 : ℝ) / (1.295212 * 12515) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036075257148 : ℝ) / (1.29521 * 12515) := by gcongr
      _ ≤ (0.000255670283 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12515 BstLean.Part154.csC) ≤ 0.001022746500 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12515 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12515 BstLean.Part154.csC) (piBar (rhoBar 12515 BstLean.Part154.csC)) ≤ 0.000195282824 ∧
    cc1 (rhoBar 12515 BstLean.Part154.csC) (piBar (rhoBar 12515 BstLean.Part154.csC)) ≤ 0.000124259729 ∧
    cc2 (rhoBar 12515 BstLean.Part154.csC) ≤ 0.000072133691 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12515 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12515 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12515 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12515 BstLean.Part154.csC * nuR (rhoBar 12515 BstLean.Part154.csC)) ≤ 0.000511356908 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000255670283 : ℝ) * 0.001022746500 := by gcongr
      _ ≤ (0.000511356908 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12515 BstLean.Part154.csC) * nuR (rhoBar 12515 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001022746500 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12515 BstLean.Part154.csC) * rhoBar 12515 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000255670283 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000255670283 / 2 + 0.399 * 0.001022746500 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000195282824 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000511356908 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124259729 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000255670283 / 1.414213562 := by gcongr
      _ ≤ (0.000072133691 : ℝ) := by norm_num

end BstLean.Part269.N12515

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12515
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12515 BstLean.Part154.csC) (piBar (rhoBar 12515 BstLean.Part154.csC)) ≤ 1.64689E-7 := by
  have hr0 : 0 ≤ rhoBar 12515 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12515 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12515 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12515 BstLean.Part154.csC) (piBar (rhoBar 12515 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12515 BstLean.Part154.csC) (piBar (rhoBar 12515 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12515 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000195282824 : ℝ) ^ 2 + 0.000124259729 ^ 2 + 3 * 0.000072133691 ^ 2 +
        2 * 0.797885 * 0.000195282824 * 0.000124259729 + 2 * 0.000195282824 * 0.000072133691 +
        4 * 0.797885 * 0.000124259729 * 0.000072133691 := by gcongr
    _ ≤ (1.64689E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12515 BstLean.Part154.csC Θ ≤ 0.002669539226 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12515 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12515 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12515 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12515 BstLean.Part154.csC) (piBar (rhoBar 12515 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12515 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036075257148 * 1.64689E-7 / (0.000255669887 : ℝ) := by gcongr
    _ ≤ 0.002669539226 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12515 BstLean.Part154.csC Θ ≤ 0.002962747350 + 0.000674546292 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12515 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12515 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12515 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036075257148 : ℝ) * ((2 * Θ * 0.000255670283 +
        (6863 / 10000) * 0.000255670283 * 12515 * 0.001022746500) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002962747350 + 0.000674546292 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12515 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12515 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12515 0.011 Θ ∧ gammaRatio 12515 0.011 Θ ≤ 0.000087892832 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12515 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036075257148 : ℝ) * 0.525 / ((1 - 0.011) * 12515) := by gcongr
      _ ≤ (0.000087892832 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12515 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12515 0.011 Θ) :=
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
    badAllowance 12515 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000774418828 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12515 BstLean.Part154.csC) 1.22 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 2 (rhoBar 12515 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12515 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12515 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12515 0.011 Θ) 1.12 ≤ 3.3895E-8 := by
    have he : (17.2 : ℝ) ≤ gap 1 (gammaRatio 12515 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12515 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12515 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12515 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12515 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036075257148 : ℝ) * 12515 *
        (2.7751E-8 / 1.1045361 + 3.3895E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000774418828 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12515 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003737166178 + 0.003344085518 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12515

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12515
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12515 BstLean.Part154.csC) (piBar (rhoBar 12515 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12515 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12515 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12515 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12515 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12515 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12515 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12515 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12515 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12515 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12515 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12515 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12515 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12515 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12515 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052875029939 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12515) ≤ 0.010675182461 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12515 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036075257148)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010675182461 + 2 * 0.737676 / 12515) := by gcongr
    _ ≤ (0.052875029939 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12515 12 ≤ 0.0015 := by
  exact BstLean.Part269.S6.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12515

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12515
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560495078369 : ℝ) ≤ plow 12515 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12515) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052999411075)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001401508094) : eMP 12515 0.011 xi bn ≤ 0.001206311428 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12515 : ℝ) * (1 - 0.011))) ≤ 0.000596429606 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001401508094 / (12515 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000596429606 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000596429606 : ℝ) + 3.141593 * 0.052999411075 / (12515 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001206311428 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052999411075)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001401508094) : PiBarMP 12515 12 0.011 xi bn ≤ 0.162450835474 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12515 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037436721198 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.253471855938 : ℝ) ≤ √((12515 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.870460801768 : ℝ) ≤ √(12515 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12515) ≤ 0.124540545940 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037436721198 + 0.052999411075 * 1.772454 / (2 * (111.253471855938 : ℝ))) * (1 + 0.001206311428) +
        8 / (12515 * 111.870460801768) + 0.124540545940 := by gcongr
    _ ≤ (0.162450835474 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052999411075)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001401508094) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283091039537) :
    parallelOracle 12515 0.011 xi bn cd ≤ 0.163456602575 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12515 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12515 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560495078369 : ℝ) ≤ plow 12515 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.870460801768 : ℝ) ≤ √(12515 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.283091039537 : ℝ) / (2 * 0.560495078369 * 111.870460801768)) * 0.162450835474 +
        0.283091039537 ^ 2 / (2 * 0.560495078369 * 111.870460801768) := by gcongr
    _ ≤ (0.163456602575 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052999411075) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001401508094)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283091039537) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12515 12515 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560495078369 : ℝ) ≤ plow 12515 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.870460801768 : ℝ) ≤ √(12515 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12515 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12515 Θ 1.22 ≤ 0.011853893249 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.870460801768 := by gcongr <;> linarith
      _ ≤ (0.011853893249 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12515 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12515 12515 0.011 ≤ 0.008544588773 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12515 12515 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12515 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12515 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12515 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12515 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163456602575 + 0.011853893249 + (0.008544588773 : ℝ) *
        (1 + 2 * (0.283091039537 + 0.011853893249) / (0.560495078369 * 111.870460801768))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12515]

end BstLean.Part269.N12515

/-! The original eight local profiles supply actual 12515 moment certificates. -/
namespace BstLean.Part269.N12515
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12515 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12515 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12515 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052999411075 ∧
    0 ≤ bN 12515 BstLean.Part154.csC (groupTheta g) ∧ bN 12515 BstLean.Part154.csC (groupTheta g) ≤ 0.001401508094 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12515 12515 0.011
      (momentAllowance 12515 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12515 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12515 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12515 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12515 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12515 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230216009598 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12515 0.011
      (momentAllowance 12515 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12515 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12515
/-! The actual computed-centre upper energy formula at 12515. -/
namespace BstLean.Part269.N12515
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12515

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12515
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12515)
open BstLean.Part268 (cell12515)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086049550992
  | 2 => 0.087003038547
  | 3 => 0.087956305659
  | 4 => 0.088911142593
  | 5 => 0.089869701505
  | 6 => 0.090834548453
  | 7 => 0.091808719961
  | 8 => 0.092795784157
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12515 12515 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12515 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003740909217 + 0.003348232271 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S6.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12515

/-! Actual upper energy certificates on all 43 source endpoints at 12515. -/
namespace BstLean.Part269.N12515
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12515)
open BstLean.Part268 (cell12515)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12515 (gMinus 12515) (1 - (cell12515 i).lower) ≤ 1 ∧
    energyUpper 12515 (gMinus 12515) (BstLean.Part211.gPlus 12515)
      (finiteEnergy 12515 12515 0.011) (1 - (cell12515 i).lower) ≤
      (cell12515 i).energy := by
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
      have E := BstLean.Part269.S6.uniformEnergy10 (n := 12515) (by norm_num)
        (q := 1 - (cell12515 ⟨10,by decide⟩).lower)
        (by norm_num [cell12515]) (by norm_num [cell12515])
      exact ⟨E.1,E.2.trans (by norm_num [cell12515])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy11 (n := 12515) (by norm_num)
        (q := 1 - (cell12515 ⟨11,by decide⟩).lower)
        (by norm_num [cell12515]) (by norm_num [cell12515])
      exact ⟨E.1,E.2.trans (by norm_num [cell12515])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy12 (n := 12515) (by norm_num)
        (q := 1 - (cell12515 ⟨12,by decide⟩).lower)
        (by norm_num [cell12515]) (by norm_num [cell12515])
      exact ⟨E.1,E.2.trans (by norm_num [cell12515])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy13 (n := 12515) (by norm_num)
        (q := 1 - (cell12515 ⟨13,by decide⟩).lower)
        (by norm_num [cell12515]) (by norm_num [cell12515])
      exact ⟨E.1,E.2.trans (by norm_num [cell12515])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy14 (n := 12515) (by norm_num)
        (q := 1 - (cell12515 ⟨14,by decide⟩).lower)
        (by norm_num [cell12515]) (by norm_num [cell12515])
      exact ⟨E.1,E.2.trans (by norm_num [cell12515])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy15 (n := 12515) (by norm_num)
        (q := 1 - (cell12515 ⟨15,by decide⟩).lower)
        (by norm_num [cell12515]) (by norm_num [cell12515])
      exact ⟨E.1,E.2.trans (by norm_num [cell12515])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy16 (n := 12515) (by norm_num)
        (q := 1 - (cell12515 ⟨16,by decide⟩).lower)
        (by norm_num [cell12515]) (by norm_num [cell12515])
      exact ⟨E.1,E.2.trans (by norm_num [cell12515])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy17 (n := 12515) (by norm_num)
        (q := 1 - (cell12515 ⟨17,by decide⟩).lower)
        (by norm_num [cell12515]) (by norm_num [cell12515])
      exact ⟨E.1,E.2.trans (by norm_num [cell12515])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy18 (n := 12515) (by norm_num)
        (q := 1 - (cell12515 ⟨18,by decide⟩).lower)
        (by norm_num [cell12515]) (by norm_num [cell12515])
      exact ⟨E.1,E.2.trans (by norm_num [cell12515])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy19 (n := 12515) (by norm_num)
        (q := 1 - (cell12515 ⟨19,by decide⟩).lower)
        (by norm_num [cell12515]) (by norm_num [cell12515])
      exact ⟨E.1,E.2.trans (by norm_num [cell12515])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy20 (n := 12515) (by norm_num)
        (q := 1 - (cell12515 ⟨20,by decide⟩).lower)
        (by norm_num [cell12515]) (by norm_num [cell12515])
      exact ⟨E.1,E.2.trans (by norm_num [cell12515])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy21 (n := 12515) (by norm_num)
        (q := 1 - (cell12515 ⟨21,by decide⟩).lower)
        (by norm_num [cell12515]) (by norm_num [cell12515])
      exact ⟨E.1,E.2.trans (by norm_num [cell12515])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy22 (n := 12515) (by norm_num)
        (q := 1 - (cell12515 ⟨22,by decide⟩).lower)
        (by norm_num [cell12515]) (by norm_num [cell12515])
      exact ⟨E.1,E.2.trans (by norm_num [cell12515])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy23 (n := 12515) (by norm_num)
        (q := 1 - (cell12515 ⟨23,by decide⟩).lower)
        (by norm_num [cell12515]) (by norm_num [cell12515])
      exact ⟨E.1,E.2.trans (by norm_num [cell12515])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy24 (n := 12515) (by norm_num)
        (q := 1 - (cell12515 ⟨24,by decide⟩).lower)
        (by norm_num [cell12515]) (by norm_num [cell12515])
      exact ⟨E.1,E.2.trans (by norm_num [cell12515])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy25 (n := 12515) (by norm_num)
        (q := 1 - (cell12515 ⟨25,by decide⟩).lower)
        (by norm_num [cell12515]) (by norm_num [cell12515])
      exact ⟨E.1,E.2.trans (by norm_num [cell12515])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy26 (n := 12515) (by norm_num)
        (q := 1 - (cell12515 ⟨26,by decide⟩).lower)
        (by norm_num [cell12515]) (by norm_num [cell12515])
      exact ⟨E.1,E.2.trans (by norm_num [cell12515])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy27 (n := 12515) (by norm_num)
        (q := 1 - (cell12515 ⟨27,by decide⟩).lower)
        (by norm_num [cell12515]) (by norm_num [cell12515])
      exact ⟨E.1,E.2.trans (by norm_num [cell12515])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy28 (n := 12515) (by norm_num)
        (q := 1 - (cell12515 ⟨28,by decide⟩).lower)
        (by norm_num [cell12515]) (by norm_num [cell12515])
      exact ⟨E.1,E.2.trans (by norm_num [cell12515])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy29 (n := 12515) (by norm_num)
        (q := 1 - (cell12515 ⟨29,by decide⟩).lower)
        (by norm_num [cell12515]) (by norm_num [cell12515])
      exact ⟨E.1,E.2.trans (by norm_num [cell12515])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy30 (n := 12515) (by norm_num)
        (q := 1 - (cell12515 ⟨30,by decide⟩).lower)
        (by norm_num [cell12515]) (by norm_num [cell12515])
      exact ⟨E.1,E.2.trans (by norm_num [cell12515])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy31 (n := 12515) (by norm_num)
        (q := 1 - (cell12515 ⟨31,by decide⟩).lower)
        (by norm_num [cell12515]) (by norm_num [cell12515])
      exact ⟨E.1,E.2.trans (by norm_num [cell12515])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy32 (n := 12515) (by norm_num)
        (q := 1 - (cell12515 ⟨32,by decide⟩).lower)
        (by norm_num [cell12515]) (by norm_num [cell12515])
      exact ⟨E.1,E.2.trans (by norm_num [cell12515])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy33 (n := 12515) (by norm_num)
        (q := 1 - (cell12515 ⟨33,by decide⟩).lower)
        (by norm_num [cell12515]) (by norm_num [cell12515])
      exact ⟨E.1,E.2.trans (by norm_num [cell12515])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy34 (n := 12515) (by norm_num)
        (q := 1 - (cell12515 ⟨34,by decide⟩).lower)
        (by norm_num [cell12515]) (by norm_num [cell12515])
      exact ⟨E.1,E.2.trans (by norm_num [cell12515])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy35 (n := 12515) (by norm_num)
        (q := 1 - (cell12515 ⟨35,by decide⟩).lower)
        (by norm_num [cell12515]) (by norm_num [cell12515])
      exact ⟨E.1,E.2.trans (by norm_num [cell12515])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy36 (n := 12515) (by norm_num)
        (q := 1 - (cell12515 ⟨36,by decide⟩).lower)
        (by norm_num [cell12515]) (by norm_num [cell12515])
      exact ⟨E.1,E.2.trans (by norm_num [cell12515])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy37 (n := 12515) (by norm_num)
        (q := 1 - (cell12515 ⟨37,by decide⟩).lower)
        (by norm_num [cell12515]) (by norm_num [cell12515])
      exact ⟨E.1,E.2.trans (by norm_num [cell12515])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy38 (n := 12515) (by norm_num)
        (q := 1 - (cell12515 ⟨38,by decide⟩).lower)
        (by norm_num [cell12515]) (by norm_num [cell12515])
      exact ⟨E.1,E.2.trans (by norm_num [cell12515])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy39 (n := 12515) (by norm_num)
        (q := 1 - (cell12515 ⟨39,by decide⟩).lower)
        (by norm_num [cell12515]) (by norm_num [cell12515])
      exact ⟨E.1,E.2.trans (by norm_num [cell12515])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy40 (n := 12515) (by norm_num)
        (q := 1 - (cell12515 ⟨40,by decide⟩).lower)
        (by norm_num [cell12515]) (by norm_num [cell12515])
      exact ⟨E.1,E.2.trans (by norm_num [cell12515])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy41 (n := 12515) (by norm_num)
        (q := 1 - (cell12515 ⟨41,by decide⟩).lower)
        (by norm_num [cell12515]) (by norm_num [cell12515])
      exact ⟨E.1,E.2.trans (by norm_num [cell12515])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy42 (n := 12515) (by norm_num)
        (q := 1 - (cell12515 ⟨42,by decide⟩).lower)
        (by norm_num [cell12515]) (by norm_num [cell12515])
      exact ⟨E.1,E.2.trans (by norm_num [cell12515])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy43 (n := 12515) (by norm_num)
        (q := 1 - (cell12515 ⟨43,by decide⟩).lower)
        (by norm_num [cell12515]) (by norm_num [cell12515])
      exact ⟨E.1,E.2.trans (by norm_num [cell12515])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy44 (n := 12515) (by norm_num)
        (q := 1 - (cell12515 ⟨44,by decide⟩).lower)
        (by norm_num [cell12515]) (by norm_num [cell12515])
      exact ⟨E.1,E.2.trans (by norm_num [cell12515])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy45 (n := 12515) (by norm_num)
        (q := 1 - (cell12515 ⟨45,by decide⟩).lower)
        (by norm_num [cell12515]) (by norm_num [cell12515])
      exact ⟨E.1,E.2.trans (by norm_num [cell12515])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy46 (n := 12515) (by norm_num)
        (q := 1 - (cell12515 ⟨46,by decide⟩).lower)
        (by norm_num [cell12515]) (by norm_num [cell12515])
      exact ⟨E.1,E.2.trans (by norm_num [cell12515])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy47 (n := 12515) (by norm_num)
        (q := 1 - (cell12515 ⟨47,by decide⟩).lower)
        (by norm_num [cell12515]) (by norm_num [cell12515])
      exact ⟨E.1,E.2.trans (by norm_num [cell12515])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy48 (n := 12515) (by norm_num)
        (q := 1 - (cell12515 ⟨48,by decide⟩).lower)
        (by norm_num [cell12515]) (by norm_num [cell12515])
      exact ⟨E.1,E.2.trans (by norm_num [cell12515])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy49 (n := 12515) (by norm_num)
        (q := 1 - (cell12515 ⟨49,by decide⟩).lower)
        (by norm_num [cell12515]) (by norm_num [cell12515])
      exact ⟨E.1,E.2.trans (by norm_num [cell12515])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy50 (n := 12515) (by norm_num)
        (q := 1 - (cell12515 ⟨50,by decide⟩).lower)
        (by norm_num [cell12515]) (by norm_num [cell12515])
      exact ⟨E.1,E.2.trans (by norm_num [cell12515])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy51 (n := 12515) (by norm_num)
        (q := 1 - (cell12515 ⟨51,by decide⟩).lower)
        (by norm_num [cell12515]) (by norm_num [cell12515])
      exact ⟨E.1,E.2.trans (by norm_num [cell12515])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy52 (n := 12515) (by norm_num)
        (q := 1 - (cell12515 ⟨52,by decide⟩).lower)
        (by norm_num [cell12515]) (by norm_num [cell12515])
      exact ⟨E.1,E.2.trans (by norm_num [cell12515])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12515

/-! Source-cell containment and simple scalar guards at 12515. -/
namespace BstLean.Part269.N12515
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12515)
open BstLean.Part268 (cell12515)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12515 ⟨10,by decide⟩).lower ∧ (cell12515 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12515 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12515 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12515 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12515 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12515 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12515,cell12515,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12515 ⟨11,by decide⟩).lower ∧ (cell12515 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12515 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12515 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12515 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12515 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12515 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12515,cell12515,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12515 ⟨12,by decide⟩).lower ∧ (cell12515 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12515 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12515 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12515 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12515 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12515 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12515,cell12515,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12515 ⟨13,by decide⟩).lower ∧ (cell12515 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12515 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12515 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12515 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12515 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12515 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12515,cell12515,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12515 ⟨14,by decide⟩).lower ∧ (cell12515 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12515 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12515 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12515 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12515 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12515 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12515,cell12515,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12515 ⟨15,by decide⟩).lower ∧ (cell12515 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12515 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12515 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12515 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12515 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12515 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12515,cell12515,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12515 ⟨16,by decide⟩).lower ∧ (cell12515 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12515 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12515 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12515 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12515 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12515 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12515,cell12515,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12515 ⟨17,by decide⟩).lower ∧ (cell12515 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12515 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12515 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12515 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12515 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12515 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12515,cell12515,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12515 ⟨18,by decide⟩).lower ∧ (cell12515 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12515 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12515 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12515 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12515 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12515 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12515,cell12515,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12515 ⟨19,by decide⟩).lower ∧ (cell12515 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12515 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12515 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12515 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12515 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12515 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12515,cell12515,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12515 ⟨20,by decide⟩).lower ∧ (cell12515 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12515 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12515 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12515 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12515 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12515 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12515,cell12515,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12515 ⟨21,by decide⟩).lower ∧ (cell12515 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12515 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12515 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12515 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12515 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12515 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12515,cell12515,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12515 ⟨22,by decide⟩).lower ∧ (cell12515 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12515 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12515 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12515 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12515 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12515 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12515,cell12515,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12515 ⟨23,by decide⟩).lower ∧ (cell12515 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12515 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12515 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12515 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12515 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12515 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12515,cell12515,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12515 ⟨24,by decide⟩).lower ∧ (cell12515 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12515 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12515 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12515 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12515 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12515 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12515,cell12515,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12515 ⟨25,by decide⟩).lower ∧ (cell12515 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12515 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12515 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12515 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12515 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12515 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12515,cell12515,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12515 ⟨26,by decide⟩).lower ∧ (cell12515 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12515 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12515 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12515 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12515 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12515 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12515,cell12515,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12515 ⟨27,by decide⟩).lower ∧ (cell12515 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12515 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12515 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12515 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12515 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12515 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12515,cell12515,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12515 ⟨28,by decide⟩).lower ∧ (cell12515 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12515 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12515 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12515 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12515 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12515 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12515,cell12515,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12515 ⟨29,by decide⟩).lower ∧ (cell12515 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12515 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12515 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12515 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12515 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12515 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12515,cell12515,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12515 ⟨30,by decide⟩).lower ∧ (cell12515 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12515 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12515 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12515 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12515 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12515 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12515,cell12515,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12515 ⟨31,by decide⟩).lower ∧ (cell12515 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12515 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12515 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12515 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12515 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12515 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12515,cell12515,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12515 ⟨32,by decide⟩).lower ∧ (cell12515 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12515 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12515 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12515 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12515 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12515 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12515,cell12515,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12515 ⟨33,by decide⟩).lower ∧ (cell12515 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12515 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12515 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12515 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12515 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12515 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12515,cell12515,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12515 ⟨34,by decide⟩).lower ∧ (cell12515 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12515 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12515 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12515 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12515 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12515 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12515,cell12515,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12515 ⟨35,by decide⟩).lower ∧ (cell12515 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12515 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12515 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12515 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12515 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12515 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12515,cell12515,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12515 ⟨36,by decide⟩).lower ∧ (cell12515 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12515 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12515 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12515 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12515 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12515 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12515,cell12515,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12515 ⟨37,by decide⟩).lower ∧ (cell12515 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12515 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12515 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12515 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12515 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12515 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12515,cell12515,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12515 ⟨38,by decide⟩).lower ∧ (cell12515 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12515 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12515 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12515 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12515 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12515 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12515,cell12515,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12515 ⟨39,by decide⟩).lower ∧ (cell12515 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12515 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12515 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12515 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12515 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12515 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12515,cell12515,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12515 ⟨40,by decide⟩).lower ∧ (cell12515 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12515 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12515 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12515 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12515 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12515 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12515,cell12515,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12515 ⟨41,by decide⟩).lower ∧ (cell12515 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12515 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12515 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12515 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12515 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12515 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12515,cell12515,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12515 ⟨42,by decide⟩).lower ∧ (cell12515 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12515 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12515 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12515 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12515 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12515 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12515,cell12515,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12515 ⟨43,by decide⟩).lower ∧ (cell12515 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12515 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12515 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12515 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12515 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12515 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12515,cell12515,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12515 ⟨44,by decide⟩).lower ∧ (cell12515 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12515 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12515 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12515 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12515 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12515 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12515,cell12515,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12515 ⟨45,by decide⟩).lower ∧ (cell12515 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12515 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12515 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12515 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12515 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12515 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12515,cell12515,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12515 ⟨46,by decide⟩).lower ∧ (cell12515 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12515 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12515 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12515 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12515 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12515 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12515,cell12515,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12515 ⟨47,by decide⟩).lower ∧ (cell12515 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12515 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12515 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12515 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12515 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12515 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12515,cell12515,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12515 ⟨48,by decide⟩).lower ∧ (cell12515 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12515 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12515 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12515 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12515 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12515 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12515,cell12515,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12515 ⟨49,by decide⟩).lower ∧ (cell12515 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12515 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12515 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12515 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12515 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12515 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12515,cell12515,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12515 ⟨50,by decide⟩).lower ∧ (cell12515 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12515 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12515 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12515 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12515 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12515 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12515,cell12515,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12515 ⟨51,by decide⟩).lower ∧ (cell12515 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12515 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12515 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12515 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12515 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12515 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12515,cell12515,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12515 ⟨52,by decide⟩).lower ∧ (cell12515 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12515 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12515 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12515 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12515 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12515 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12515,cell12515,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12515 i).lower ∧
    (cell12515 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12515 i).upper ≤ (0.532 : ℝ) ∧
    (cell12515 i).centre ≤ (0.1 : ℝ) ∧ (cell12515 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12515 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12515 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12515

/-! The local source numeric instances at 12515 have no network premises. -/
namespace BstLean.Part269.N12515
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12515)
open BstLean.Part268 (cell12515)

noncomputable def sourceNumerics12515 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12515 (cell12515 i)
      scalarRow12515.M scalarRow12515.H scalarRow12515.xi := by
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
    energy_allowance := scalarRow12515.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12515]
    centre_nonneg := (scalarRow12515.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D6.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12515])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12515
/-! Actual 12516 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12516
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12516 ≤ (1.036073803186 : ℝ) := by
  have hr : (111.874930167575 : ℝ) ≤ √(12516 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.874930167575 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12516 12516 (11 / 1000) ≤
    (0.008544247417 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12516) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.874930167575 : ℝ) ≤ √(12516 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12516)
  have hdiv : K / √(12516 : ℝ) ≤ K / 111.874930167575 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.874930167575 ≤ (0.008544247417 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12516.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12516 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12516 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12516 := gPlus_lower 12516
end BstLean.Part269.N12516

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12516
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036073803185 : ℝ) ≤ wn 12516 := by
  have hn : √(12516 : ℝ) ≤ 111.874930167576 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12516 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.874930167576 ≤ 2 / √(12516 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000255649101 : ℝ) ≤ rhoBar 12516 BstLean.Part154.csC ∧
    rhoBar 12516 BstLean.Part154.csC ≤ 0.000255649496 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036073803185 : ℝ) / (1.295212 * 12516) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036073803186 : ℝ) / (1.29521 * 12516) := by gcongr
      _ ≤ (0.000255649496 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12516 BstLean.Part154.csC) ≤ 0.001022663341 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12516 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12516 BstLean.Part154.csC) (piBar (rhoBar 12516 BstLean.Part154.csC)) ≤ 0.000195266946 ∧
    cc1 (rhoBar 12516 BstLean.Part154.csC) (piBar (rhoBar 12516 BstLean.Part154.csC)) ≤ 0.000124249626 ∧
    cc2 (rhoBar 12516 BstLean.Part154.csC) ≤ 0.000072127826 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12516 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12516 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12516 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12516 BstLean.Part154.csC * nuR (rhoBar 12516 BstLean.Part154.csC)) ≤ 0.000511315331 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000255649496 : ℝ) * 0.001022663341 := by gcongr
      _ ≤ (0.000511315331 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12516 BstLean.Part154.csC) * nuR (rhoBar 12516 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001022663341 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12516 BstLean.Part154.csC) * rhoBar 12516 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000255649496 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000255649496 / 2 + 0.399 * 0.001022663341 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000195266946 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000511315331 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124249626 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000255649496 / 1.414213562 := by gcongr
      _ ≤ (0.000072127826 : ℝ) := by norm_num

end BstLean.Part269.N12516

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12516
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12516 BstLean.Part154.csC) (piBar (rhoBar 12516 BstLean.Part154.csC)) ≤ 1.64662E-7 := by
  have hr0 : 0 ≤ rhoBar 12516 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12516 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12516 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12516 BstLean.Part154.csC) (piBar (rhoBar 12516 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12516 BstLean.Part154.csC) (piBar (rhoBar 12516 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12516 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000195266946 : ℝ) ^ 2 + 0.000124249626 ^ 2 + 3 * 0.000072127826 ^ 2 +
        2 * 0.797885 * 0.000195266946 * 0.000124249626 + 2 * 0.000195266946 * 0.000072127826 +
        4 * 0.797885 * 0.000124249626 * 0.000072127826 := by gcongr
    _ ≤ (1.64662E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12516 BstLean.Part154.csC Θ ≤ 0.002669314837 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12516 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12516 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12516 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12516 BstLean.Part154.csC) (piBar (rhoBar 12516 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12516 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036073803186 * 1.64662E-7 / (0.000255649101 : ℝ) := by gcongr
    _ ≤ 0.002669314837 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12516 BstLean.Part154.csC Θ ≤ 0.002962498127 + 0.000674490502 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12516 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12516 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12516 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036073803186 : ℝ) * ((2 * Θ * 0.000255649496 +
        (6863 / 10000) * 0.000255649496 * 12516 * 0.001022663341) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002962498127 + 0.000674490502 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12516 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12516 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12516 0.011 Θ ∧ gammaRatio 12516 0.011 Θ ≤ 0.000087885686 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12516 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036073803186 : ℝ) * 0.525 / ((1 - 0.011) * 12516) := by gcongr
      _ ≤ (0.000087885686 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12516 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12516 0.011 Θ) :=
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
    badAllowance 12516 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000774418828 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12516 BstLean.Part154.csC) 1.22 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 2 (rhoBar 12516 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12516 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12516 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12516 0.011 Θ) 1.12 ≤ 3.3895E-8 := by
    have he : (17.2 : ℝ) ≤ gap 1 (gammaRatio 12516 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12516 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12516 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12516 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12516 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036073803186 : ℝ) * 12516 *
        (2.7751E-8 / 1.1045361 + 3.3895E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000774418828 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12516 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003736916955 + 0.003343805339 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12516

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12516
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12516 BstLean.Part154.csC) (piBar (rhoBar 12516 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12516 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12516 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12516 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12516 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12516 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12516 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12516 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12516 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12516 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12516 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12516 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12516 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12516 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12516 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052872894533 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12516) ≤ 0.010674755992 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12516 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036073803186)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010674755992 + 2 * 0.737676 / 12516) := by gcongr
    _ ≤ (0.052872894533 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12516 12 ≤ 0.0015 := by
  exact BstLean.Part269.S6.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12516

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12516
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560495124936 : ℝ) ≤ plow 12516 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12516) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052999014758)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001401390290) : eMP 12516 0.011 xi bn ≤ 0.001206212467 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12516 : ℝ) * (1 - 0.011))) ≤ 0.000596380713 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001401390290 / (12516 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000596380713 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000596380713 : ℝ) + 3.141593 * 0.052999014758 / (12516 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001206212467 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052999014758)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001401390290) : PiBarMP 12516 12 0.011 xi bn ≤ 0.162444260337 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12516 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037435147790 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.257916572260 : ℝ) ≤ √((12516 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.874930167575 : ℝ) ≤ √(12516 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12516) ≤ 0.124535570587 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037435147790 + 0.052999014758 * 1.772454 / (2 * (111.257916572260 : ℝ))) * (1 + 0.001206212467) +
        8 / (12516 * 111.874930167575) + 0.124535570587 := by gcongr
    _ ≤ (0.162444260337 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052999014758)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001401390290) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283088043379) :
    parallelOracle 12516 0.011 xi bn cd ≤ 0.163449954925 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12516 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12516 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560495124936 : ℝ) ≤ plow 12516 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.874930167575 : ℝ) ≤ √(12516 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.283088043379 : ℝ) / (2 * 0.560495124936 * 111.874930167575)) * 0.162444260337 +
        0.283088043379 ^ 2 / (2 * 0.560495124936 * 111.874930167575) := by gcongr
    _ ≤ (0.163449954925 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052999014758) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001401390290)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283088043379) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12516 12516 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560495124936 : ℝ) ≤ plow 12516 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.874930167575 : ℝ) ≤ √(12516 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12516 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12516 Θ 1.22 ≤ 0.011853419690 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.874930167575 := by gcongr <;> linarith
      _ ≤ (0.011853419690 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12516 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12516 12516 0.011 ≤ 0.008544247417 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12516 12516 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12516 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12516 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12516 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12516 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163449954925 + 0.011853419690 + (0.008544247417 : ℝ) *
        (1 + 2 * (0.283088043379 + 0.011853419690) / (0.560495124936 * 111.874930167575))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12516]

end BstLean.Part269.N12516

/-! The original eight local profiles supply actual 12516 moment certificates. -/
namespace BstLean.Part269.N12516
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12516 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12516 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12516 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052999014758 ∧
    0 ≤ bN 12516 BstLean.Part154.csC (groupTheta g) ∧ bN 12516 BstLean.Part154.csC (groupTheta g) ≤ 0.001401390290 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12516 12516 0.011
      (momentAllowance 12516 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12516 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12516 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12516 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12516 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12516 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230215148846 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12516 0.011
      (momentAllowance 12516 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12516 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12516
/-! The actual computed-centre upper energy formula at 12516. -/
namespace BstLean.Part269.N12516
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12516

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12516
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12516)
open BstLean.Part268 (cell12516)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086046414445
  | 2 => 0.086999839143
  | 3 => 0.087953033406
  | 4 => 0.088907785261
  | 5 => 0.089866244246
  | 6 => 0.090830973365
  | 7 => 0.091805005616
  | 8 => 0.092791905072
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12516 12516 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12516 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003740909217 + 0.003348232271 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S6.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12516

/-! Actual upper energy certificates on all 43 source endpoints at 12516. -/
namespace BstLean.Part269.N12516
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12516)
open BstLean.Part268 (cell12516)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12516 (gMinus 12516) (1 - (cell12516 i).lower) ≤ 1 ∧
    energyUpper 12516 (gMinus 12516) (BstLean.Part211.gPlus 12516)
      (finiteEnergy 12516 12516 0.011) (1 - (cell12516 i).lower) ≤
      (cell12516 i).energy := by
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
      have E := BstLean.Part269.S6.uniformEnergy10 (n := 12516) (by norm_num)
        (q := 1 - (cell12516 ⟨10,by decide⟩).lower)
        (by norm_num [cell12516]) (by norm_num [cell12516])
      exact ⟨E.1,E.2.trans (by norm_num [cell12516])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy11 (n := 12516) (by norm_num)
        (q := 1 - (cell12516 ⟨11,by decide⟩).lower)
        (by norm_num [cell12516]) (by norm_num [cell12516])
      exact ⟨E.1,E.2.trans (by norm_num [cell12516])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy12 (n := 12516) (by norm_num)
        (q := 1 - (cell12516 ⟨12,by decide⟩).lower)
        (by norm_num [cell12516]) (by norm_num [cell12516])
      exact ⟨E.1,E.2.trans (by norm_num [cell12516])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy13 (n := 12516) (by norm_num)
        (q := 1 - (cell12516 ⟨13,by decide⟩).lower)
        (by norm_num [cell12516]) (by norm_num [cell12516])
      exact ⟨E.1,E.2.trans (by norm_num [cell12516])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy14 (n := 12516) (by norm_num)
        (q := 1 - (cell12516 ⟨14,by decide⟩).lower)
        (by norm_num [cell12516]) (by norm_num [cell12516])
      exact ⟨E.1,E.2.trans (by norm_num [cell12516])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy15 (n := 12516) (by norm_num)
        (q := 1 - (cell12516 ⟨15,by decide⟩).lower)
        (by norm_num [cell12516]) (by norm_num [cell12516])
      exact ⟨E.1,E.2.trans (by norm_num [cell12516])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy16 (n := 12516) (by norm_num)
        (q := 1 - (cell12516 ⟨16,by decide⟩).lower)
        (by norm_num [cell12516]) (by norm_num [cell12516])
      exact ⟨E.1,E.2.trans (by norm_num [cell12516])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy17 (n := 12516) (by norm_num)
        (q := 1 - (cell12516 ⟨17,by decide⟩).lower)
        (by norm_num [cell12516]) (by norm_num [cell12516])
      exact ⟨E.1,E.2.trans (by norm_num [cell12516])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy18 (n := 12516) (by norm_num)
        (q := 1 - (cell12516 ⟨18,by decide⟩).lower)
        (by norm_num [cell12516]) (by norm_num [cell12516])
      exact ⟨E.1,E.2.trans (by norm_num [cell12516])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy19 (n := 12516) (by norm_num)
        (q := 1 - (cell12516 ⟨19,by decide⟩).lower)
        (by norm_num [cell12516]) (by norm_num [cell12516])
      exact ⟨E.1,E.2.trans (by norm_num [cell12516])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy20 (n := 12516) (by norm_num)
        (q := 1 - (cell12516 ⟨20,by decide⟩).lower)
        (by norm_num [cell12516]) (by norm_num [cell12516])
      exact ⟨E.1,E.2.trans (by norm_num [cell12516])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy21 (n := 12516) (by norm_num)
        (q := 1 - (cell12516 ⟨21,by decide⟩).lower)
        (by norm_num [cell12516]) (by norm_num [cell12516])
      exact ⟨E.1,E.2.trans (by norm_num [cell12516])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy22 (n := 12516) (by norm_num)
        (q := 1 - (cell12516 ⟨22,by decide⟩).lower)
        (by norm_num [cell12516]) (by norm_num [cell12516])
      exact ⟨E.1,E.2.trans (by norm_num [cell12516])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy23 (n := 12516) (by norm_num)
        (q := 1 - (cell12516 ⟨23,by decide⟩).lower)
        (by norm_num [cell12516]) (by norm_num [cell12516])
      exact ⟨E.1,E.2.trans (by norm_num [cell12516])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy24 (n := 12516) (by norm_num)
        (q := 1 - (cell12516 ⟨24,by decide⟩).lower)
        (by norm_num [cell12516]) (by norm_num [cell12516])
      exact ⟨E.1,E.2.trans (by norm_num [cell12516])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy25 (n := 12516) (by norm_num)
        (q := 1 - (cell12516 ⟨25,by decide⟩).lower)
        (by norm_num [cell12516]) (by norm_num [cell12516])
      exact ⟨E.1,E.2.trans (by norm_num [cell12516])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy26 (n := 12516) (by norm_num)
        (q := 1 - (cell12516 ⟨26,by decide⟩).lower)
        (by norm_num [cell12516]) (by norm_num [cell12516])
      exact ⟨E.1,E.2.trans (by norm_num [cell12516])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy27 (n := 12516) (by norm_num)
        (q := 1 - (cell12516 ⟨27,by decide⟩).lower)
        (by norm_num [cell12516]) (by norm_num [cell12516])
      exact ⟨E.1,E.2.trans (by norm_num [cell12516])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy28 (n := 12516) (by norm_num)
        (q := 1 - (cell12516 ⟨28,by decide⟩).lower)
        (by norm_num [cell12516]) (by norm_num [cell12516])
      exact ⟨E.1,E.2.trans (by norm_num [cell12516])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy29 (n := 12516) (by norm_num)
        (q := 1 - (cell12516 ⟨29,by decide⟩).lower)
        (by norm_num [cell12516]) (by norm_num [cell12516])
      exact ⟨E.1,E.2.trans (by norm_num [cell12516])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy30 (n := 12516) (by norm_num)
        (q := 1 - (cell12516 ⟨30,by decide⟩).lower)
        (by norm_num [cell12516]) (by norm_num [cell12516])
      exact ⟨E.1,E.2.trans (by norm_num [cell12516])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy31 (n := 12516) (by norm_num)
        (q := 1 - (cell12516 ⟨31,by decide⟩).lower)
        (by norm_num [cell12516]) (by norm_num [cell12516])
      exact ⟨E.1,E.2.trans (by norm_num [cell12516])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy32 (n := 12516) (by norm_num)
        (q := 1 - (cell12516 ⟨32,by decide⟩).lower)
        (by norm_num [cell12516]) (by norm_num [cell12516])
      exact ⟨E.1,E.2.trans (by norm_num [cell12516])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy33 (n := 12516) (by norm_num)
        (q := 1 - (cell12516 ⟨33,by decide⟩).lower)
        (by norm_num [cell12516]) (by norm_num [cell12516])
      exact ⟨E.1,E.2.trans (by norm_num [cell12516])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy34 (n := 12516) (by norm_num)
        (q := 1 - (cell12516 ⟨34,by decide⟩).lower)
        (by norm_num [cell12516]) (by norm_num [cell12516])
      exact ⟨E.1,E.2.trans (by norm_num [cell12516])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy35 (n := 12516) (by norm_num)
        (q := 1 - (cell12516 ⟨35,by decide⟩).lower)
        (by norm_num [cell12516]) (by norm_num [cell12516])
      exact ⟨E.1,E.2.trans (by norm_num [cell12516])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy36 (n := 12516) (by norm_num)
        (q := 1 - (cell12516 ⟨36,by decide⟩).lower)
        (by norm_num [cell12516]) (by norm_num [cell12516])
      exact ⟨E.1,E.2.trans (by norm_num [cell12516])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy37 (n := 12516) (by norm_num)
        (q := 1 - (cell12516 ⟨37,by decide⟩).lower)
        (by norm_num [cell12516]) (by norm_num [cell12516])
      exact ⟨E.1,E.2.trans (by norm_num [cell12516])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy38 (n := 12516) (by norm_num)
        (q := 1 - (cell12516 ⟨38,by decide⟩).lower)
        (by norm_num [cell12516]) (by norm_num [cell12516])
      exact ⟨E.1,E.2.trans (by norm_num [cell12516])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy39 (n := 12516) (by norm_num)
        (q := 1 - (cell12516 ⟨39,by decide⟩).lower)
        (by norm_num [cell12516]) (by norm_num [cell12516])
      exact ⟨E.1,E.2.trans (by norm_num [cell12516])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy40 (n := 12516) (by norm_num)
        (q := 1 - (cell12516 ⟨40,by decide⟩).lower)
        (by norm_num [cell12516]) (by norm_num [cell12516])
      exact ⟨E.1,E.2.trans (by norm_num [cell12516])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy41 (n := 12516) (by norm_num)
        (q := 1 - (cell12516 ⟨41,by decide⟩).lower)
        (by norm_num [cell12516]) (by norm_num [cell12516])
      exact ⟨E.1,E.2.trans (by norm_num [cell12516])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy42 (n := 12516) (by norm_num)
        (q := 1 - (cell12516 ⟨42,by decide⟩).lower)
        (by norm_num [cell12516]) (by norm_num [cell12516])
      exact ⟨E.1,E.2.trans (by norm_num [cell12516])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy43 (n := 12516) (by norm_num)
        (q := 1 - (cell12516 ⟨43,by decide⟩).lower)
        (by norm_num [cell12516]) (by norm_num [cell12516])
      exact ⟨E.1,E.2.trans (by norm_num [cell12516])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy44 (n := 12516) (by norm_num)
        (q := 1 - (cell12516 ⟨44,by decide⟩).lower)
        (by norm_num [cell12516]) (by norm_num [cell12516])
      exact ⟨E.1,E.2.trans (by norm_num [cell12516])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy45 (n := 12516) (by norm_num)
        (q := 1 - (cell12516 ⟨45,by decide⟩).lower)
        (by norm_num [cell12516]) (by norm_num [cell12516])
      exact ⟨E.1,E.2.trans (by norm_num [cell12516])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy46 (n := 12516) (by norm_num)
        (q := 1 - (cell12516 ⟨46,by decide⟩).lower)
        (by norm_num [cell12516]) (by norm_num [cell12516])
      exact ⟨E.1,E.2.trans (by norm_num [cell12516])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy47 (n := 12516) (by norm_num)
        (q := 1 - (cell12516 ⟨47,by decide⟩).lower)
        (by norm_num [cell12516]) (by norm_num [cell12516])
      exact ⟨E.1,E.2.trans (by norm_num [cell12516])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy48 (n := 12516) (by norm_num)
        (q := 1 - (cell12516 ⟨48,by decide⟩).lower)
        (by norm_num [cell12516]) (by norm_num [cell12516])
      exact ⟨E.1,E.2.trans (by norm_num [cell12516])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy49 (n := 12516) (by norm_num)
        (q := 1 - (cell12516 ⟨49,by decide⟩).lower)
        (by norm_num [cell12516]) (by norm_num [cell12516])
      exact ⟨E.1,E.2.trans (by norm_num [cell12516])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy50 (n := 12516) (by norm_num)
        (q := 1 - (cell12516 ⟨50,by decide⟩).lower)
        (by norm_num [cell12516]) (by norm_num [cell12516])
      exact ⟨E.1,E.2.trans (by norm_num [cell12516])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy51 (n := 12516) (by norm_num)
        (q := 1 - (cell12516 ⟨51,by decide⟩).lower)
        (by norm_num [cell12516]) (by norm_num [cell12516])
      exact ⟨E.1,E.2.trans (by norm_num [cell12516])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy52 (n := 12516) (by norm_num)
        (q := 1 - (cell12516 ⟨52,by decide⟩).lower)
        (by norm_num [cell12516]) (by norm_num [cell12516])
      exact ⟨E.1,E.2.trans (by norm_num [cell12516])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12516

/-! Source-cell containment and simple scalar guards at 12516. -/
namespace BstLean.Part269.N12516
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12516)
open BstLean.Part268 (cell12516)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12516 ⟨10,by decide⟩).lower ∧ (cell12516 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12516 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12516 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12516 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12516 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12516 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12516,cell12516,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12516 ⟨11,by decide⟩).lower ∧ (cell12516 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12516 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12516 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12516 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12516 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12516 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12516,cell12516,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12516 ⟨12,by decide⟩).lower ∧ (cell12516 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12516 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12516 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12516 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12516 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12516 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12516,cell12516,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12516 ⟨13,by decide⟩).lower ∧ (cell12516 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12516 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12516 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12516 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12516 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12516 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12516,cell12516,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12516 ⟨14,by decide⟩).lower ∧ (cell12516 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12516 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12516 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12516 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12516 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12516 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12516,cell12516,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12516 ⟨15,by decide⟩).lower ∧ (cell12516 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12516 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12516 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12516 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12516 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12516 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12516,cell12516,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12516 ⟨16,by decide⟩).lower ∧ (cell12516 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12516 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12516 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12516 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12516 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12516 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12516,cell12516,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12516 ⟨17,by decide⟩).lower ∧ (cell12516 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12516 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12516 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12516 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12516 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12516 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12516,cell12516,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12516 ⟨18,by decide⟩).lower ∧ (cell12516 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12516 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12516 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12516 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12516 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12516 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12516,cell12516,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12516 ⟨19,by decide⟩).lower ∧ (cell12516 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12516 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12516 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12516 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12516 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12516 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12516,cell12516,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12516 ⟨20,by decide⟩).lower ∧ (cell12516 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12516 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12516 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12516 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12516 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12516 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12516,cell12516,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12516 ⟨21,by decide⟩).lower ∧ (cell12516 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12516 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12516 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12516 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12516 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12516 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12516,cell12516,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12516 ⟨22,by decide⟩).lower ∧ (cell12516 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12516 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12516 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12516 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12516 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12516 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12516,cell12516,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12516 ⟨23,by decide⟩).lower ∧ (cell12516 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12516 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12516 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12516 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12516 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12516 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12516,cell12516,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12516 ⟨24,by decide⟩).lower ∧ (cell12516 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12516 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12516 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12516 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12516 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12516 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12516,cell12516,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12516 ⟨25,by decide⟩).lower ∧ (cell12516 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12516 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12516 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12516 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12516 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12516 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12516,cell12516,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12516 ⟨26,by decide⟩).lower ∧ (cell12516 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12516 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12516 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12516 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12516 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12516 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12516,cell12516,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12516 ⟨27,by decide⟩).lower ∧ (cell12516 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12516 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12516 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12516 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12516 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12516 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12516,cell12516,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12516 ⟨28,by decide⟩).lower ∧ (cell12516 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12516 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12516 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12516 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12516 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12516 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12516,cell12516,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12516 ⟨29,by decide⟩).lower ∧ (cell12516 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12516 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12516 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12516 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12516 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12516 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12516,cell12516,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12516 ⟨30,by decide⟩).lower ∧ (cell12516 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12516 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12516 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12516 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12516 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12516 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12516,cell12516,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12516 ⟨31,by decide⟩).lower ∧ (cell12516 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12516 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12516 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12516 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12516 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12516 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12516,cell12516,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12516 ⟨32,by decide⟩).lower ∧ (cell12516 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12516 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12516 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12516 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12516 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12516 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12516,cell12516,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12516 ⟨33,by decide⟩).lower ∧ (cell12516 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12516 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12516 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12516 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12516 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12516 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12516,cell12516,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12516 ⟨34,by decide⟩).lower ∧ (cell12516 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12516 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12516 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12516 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12516 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12516 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12516,cell12516,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12516 ⟨35,by decide⟩).lower ∧ (cell12516 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12516 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12516 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12516 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12516 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12516 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12516,cell12516,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12516 ⟨36,by decide⟩).lower ∧ (cell12516 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12516 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12516 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12516 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12516 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12516 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12516,cell12516,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12516 ⟨37,by decide⟩).lower ∧ (cell12516 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12516 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12516 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12516 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12516 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12516 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12516,cell12516,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12516 ⟨38,by decide⟩).lower ∧ (cell12516 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12516 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12516 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12516 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12516 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12516 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12516,cell12516,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12516 ⟨39,by decide⟩).lower ∧ (cell12516 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12516 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12516 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12516 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12516 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12516 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12516,cell12516,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12516 ⟨40,by decide⟩).lower ∧ (cell12516 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12516 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12516 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12516 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12516 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12516 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12516,cell12516,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12516 ⟨41,by decide⟩).lower ∧ (cell12516 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12516 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12516 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12516 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12516 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12516 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12516,cell12516,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12516 ⟨42,by decide⟩).lower ∧ (cell12516 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12516 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12516 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12516 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12516 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12516 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12516,cell12516,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12516 ⟨43,by decide⟩).lower ∧ (cell12516 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12516 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12516 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12516 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12516 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12516 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12516,cell12516,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12516 ⟨44,by decide⟩).lower ∧ (cell12516 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12516 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12516 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12516 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12516 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12516 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12516,cell12516,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12516 ⟨45,by decide⟩).lower ∧ (cell12516 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12516 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12516 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12516 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12516 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12516 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12516,cell12516,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12516 ⟨46,by decide⟩).lower ∧ (cell12516 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12516 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12516 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12516 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12516 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12516 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12516,cell12516,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12516 ⟨47,by decide⟩).lower ∧ (cell12516 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12516 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12516 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12516 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12516 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12516 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12516,cell12516,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12516 ⟨48,by decide⟩).lower ∧ (cell12516 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12516 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12516 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12516 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12516 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12516 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12516,cell12516,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12516 ⟨49,by decide⟩).lower ∧ (cell12516 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12516 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12516 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12516 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12516 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12516 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12516,cell12516,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12516 ⟨50,by decide⟩).lower ∧ (cell12516 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12516 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12516 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12516 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12516 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12516 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12516,cell12516,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12516 ⟨51,by decide⟩).lower ∧ (cell12516 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12516 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12516 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12516 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12516 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12516 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12516,cell12516,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12516 ⟨52,by decide⟩).lower ∧ (cell12516 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12516 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12516 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12516 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12516 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12516 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12516,cell12516,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12516 i).lower ∧
    (cell12516 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12516 i).upper ≤ (0.532 : ℝ) ∧
    (cell12516 i).centre ≤ (0.1 : ℝ) ∧ (cell12516 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12516 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12516 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12516

/-! The local source numeric instances at 12516 have no network premises. -/
namespace BstLean.Part269.N12516
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12516)
open BstLean.Part268 (cell12516)

noncomputable def sourceNumerics12516 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12516 (cell12516 i)
      scalarRow12516.M scalarRow12516.H scalarRow12516.xi := by
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
    energy_allowance := scalarRow12516.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12516]
    centre_nonneg := (scalarRow12516.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D6.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12516])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12516
/-! Actual 12517 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12517
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12517 ≤ (1.036072349399 : ℝ) := by
  have hr : (111.879399354841 : ℝ) ≤ √(12517 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.879399354841 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12517 12517 (11 / 1000) ≤
    (0.008543906102 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12517) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.879399354841 : ℝ) ≤ √(12517 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12517)
  have hdiv : K / √(12517 : ℝ) ≤ K / 111.879399354841 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.879399354841 ≤ (0.008543906102 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12517.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12517 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12517 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12517 := gPlus_lower 12517
end BstLean.Part269.N12517

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12517
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036072349398 : ℝ) ≤ wn 12517 := by
  have hn : √(12517 : ℝ) ≤ 111.879399354842 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12517 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.879399354842 ≤ 2 / √(12517 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000255628318 : ℝ) ≤ rhoBar 12517 BstLean.Part154.csC ∧
    rhoBar 12517 BstLean.Part154.csC ≤ 0.000255628714 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036072349398 : ℝ) / (1.295212 * 12517) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036072349399 : ℝ) / (1.29521 * 12517) := by gcongr
      _ ≤ (0.000255628714 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12517 BstLean.Part154.csC) ≤ 0.001022580203 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12517 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12517 BstLean.Part154.csC) (piBar (rhoBar 12517 BstLean.Part154.csC)) ≤ 0.000195251071 ∧
    cc1 (rhoBar 12517 BstLean.Part154.csC) (piBar (rhoBar 12517 BstLean.Part154.csC)) ≤ 0.000124239525 ∧
    cc2 (rhoBar 12517 BstLean.Part154.csC) ≤ 0.000072121963 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12517 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12517 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12517 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12517 BstLean.Part154.csC * nuR (rhoBar 12517 BstLean.Part154.csC)) ≤ 0.000511273765 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000255628714 : ℝ) * 0.001022580203 := by gcongr
      _ ≤ (0.000511273765 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12517 BstLean.Part154.csC) * nuR (rhoBar 12517 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001022580203 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12517 BstLean.Part154.csC) * rhoBar 12517 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000255628714 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000255628714 / 2 + 0.399 * 0.001022580203 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000195251071 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000511273765 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124239525 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000255628714 / 1.414213562 := by gcongr
      _ ≤ (0.000072121963 : ℝ) := by norm_num

end BstLean.Part269.N12517

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12517
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12517 BstLean.Part154.csC) (piBar (rhoBar 12517 BstLean.Part154.csC)) ≤ 1.64635E-7 := by
  have hr0 : 0 ≤ rhoBar 12517 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12517 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12517 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12517 BstLean.Part154.csC) (piBar (rhoBar 12517 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12517 BstLean.Part154.csC) (piBar (rhoBar 12517 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12517 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000195251071 : ℝ) ^ 2 + 0.000124239525 ^ 2 + 3 * 0.000072121963 ^ 2 +
        2 * 0.797885 * 0.000195251071 * 0.000124239525 + 2 * 0.000195251071 * 0.000072121963 +
        4 * 0.797885 * 0.000124239525 * 0.000072121963 := by gcongr
    _ ≤ (1.64635E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12517 BstLean.Part154.csC Θ ≤ 0.002669090383 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12517 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12517 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12517 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12517 BstLean.Part154.csC) (piBar (rhoBar 12517 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12517 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036072349399 * 1.64635E-7 / (0.000255628318 : ℝ) := by gcongr
    _ ≤ 0.002669090383 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12517 BstLean.Part154.csC Θ ≤ 0.002962248986 + 0.000674434726 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12517 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12517 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12517 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036072349399 : ℝ) * ((2 * Θ * 0.000255628714 +
        (6863 / 10000) * 0.000255628714 * 12517 * 0.001022580203) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002962248986 + 0.000674434726 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12517 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12517 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12517 0.011 Θ ∧ gammaRatio 12517 0.011 Θ ≤ 0.000087878542 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12517 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036072349399 : ℝ) * 0.525 / ((1 - 0.011) * 12517) := by gcongr
      _ ≤ (0.000087878542 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12517 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12517 0.011 Θ) :=
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
    badAllowance 12517 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000774418828 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12517 BstLean.Part154.csC) 1.22 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 2 (rhoBar 12517 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12517 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12517 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12517 0.011 Θ) 1.12 ≤ 3.3895E-8 := by
    have he : (17.2 : ℝ) ≤ gap 1 (gammaRatio 12517 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12517 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12517 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12517 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12517 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036072349399 : ℝ) * 12517 *
        (2.7751E-8 / 1.1045361 + 3.3895E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000774418828 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12517 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003736667814 + 0.003343525109 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12517

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12517
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12517 BstLean.Part154.csC) (piBar (rhoBar 12517 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12517 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12517 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12517 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12517 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12517 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12517 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12517 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12517 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12517 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12517 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12517 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12517 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12517 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12517 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052870759379 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12517) ≤ 0.010674329573 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12517 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036072349399)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010674329573 + 2 * 0.737676 / 12517) := by gcongr
    _ ≤ (0.052870759379 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12517 12 ≤ 0.0015 := by
  exact BstLean.Part269.S6.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12517

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12517
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560495171494 : ℝ) ≤ plow 12517 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12517) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052998618497)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001401272452) : eMP 12517 0.011 xi bn ≤ 0.001206113498 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12517 : ℝ) * (1 - 0.011))) ≤ 0.000596331816 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001401272452 / (12517 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000596331816 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000596331816 : ℝ) + 3.141593 * 0.052998618497 / (12517 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001206113498 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052998618497)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001401272452) : PiBarMP 12517 12 0.011 xi bn ≤ 0.162437685276 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12517 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037433573861 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.262361111024 : ℝ) ≤ √((12517 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.879399354841 : ℝ) ≤ √(12517 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12517) ≤ 0.124530595830 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037433573861 + 0.052998618497 * 1.772454 / (2 * (111.262361111024 : ℝ))) * (1 + 0.001206113498) +
        8 / (12517 * 111.879399354841) + 0.124530595830 := by gcongr
    _ ≤ (0.162437685276 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052998618497)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001401272452) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283085047592) :
    parallelOracle 12517 0.011 xi bn cd ≤ 0.163443307361 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12517 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12517 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560495171494 : ℝ) ≤ plow 12517 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.879399354841 : ℝ) ≤ √(12517 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.283085047592 : ℝ) / (2 * 0.560495171494 * 111.879399354841)) * 0.162437685276 +
        0.283085047592 ^ 2 / (2 * 0.560495171494 * 111.879399354841) := by gcongr
    _ ≤ (0.163443307361 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052998618497) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001401272452)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283085047592) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12517 12517 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560495171494 : ℝ) ≤ plow 12517 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.879399354841 : ℝ) ≤ √(12517 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12517 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12517 Θ 1.22 ≤ 0.011852946188 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.879399354841 := by gcongr <;> linarith
      _ ≤ (0.011852946188 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12517 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12517 12517 0.011 ≤ 0.008543906102 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12517 12517 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12517 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12517 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12517 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12517 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163443307361 + 0.011852946188 + (0.008543906102 : ℝ) *
        (1 + 2 * (0.283085047592 + 0.011852946188) / (0.560495171494 * 111.879399354841))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12517]

end BstLean.Part269.N12517

/-! The original eight local profiles supply actual 12517 moment certificates. -/
namespace BstLean.Part269.N12517
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12517 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12517 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12517 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052998618497 ∧
    0 ≤ bN 12517 BstLean.Part154.csC (groupTheta g) ∧ bN 12517 BstLean.Part154.csC (groupTheta g) ≤ 0.001401272452 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12517 12517 0.011
      (momentAllowance 12517 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12517 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12517 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12517 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12517 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12517 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230214288213 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12517 0.011
      (momentAllowance 12517 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12517 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12517
/-! The actual computed-centre upper energy formula at 12517. -/
namespace BstLean.Part269.N12517
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12517

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12517
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12517)
open BstLean.Part268 (cell12517)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086043279209
  | 2 => 0.086996641107
  | 3 => 0.087949762592
  | 4 => 0.088904429454
  | 5 => 0.089862788615
  | 6 => 0.090827400032
  | 7 => 0.091801293178
  | 8 => 0.092788028079
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12517 12517 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12517 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003740909217 + 0.003348232271 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S6.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12517

/-! Actual upper energy certificates on all 43 source endpoints at 12517. -/
namespace BstLean.Part269.N12517
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12517)
open BstLean.Part268 (cell12517)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12517 (gMinus 12517) (1 - (cell12517 i).lower) ≤ 1 ∧
    energyUpper 12517 (gMinus 12517) (BstLean.Part211.gPlus 12517)
      (finiteEnergy 12517 12517 0.011) (1 - (cell12517 i).lower) ≤
      (cell12517 i).energy := by
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
      have E := BstLean.Part269.S6.uniformEnergy10 (n := 12517) (by norm_num)
        (q := 1 - (cell12517 ⟨10,by decide⟩).lower)
        (by norm_num [cell12517]) (by norm_num [cell12517])
      exact ⟨E.1,E.2.trans (by norm_num [cell12517])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy11 (n := 12517) (by norm_num)
        (q := 1 - (cell12517 ⟨11,by decide⟩).lower)
        (by norm_num [cell12517]) (by norm_num [cell12517])
      exact ⟨E.1,E.2.trans (by norm_num [cell12517])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy12 (n := 12517) (by norm_num)
        (q := 1 - (cell12517 ⟨12,by decide⟩).lower)
        (by norm_num [cell12517]) (by norm_num [cell12517])
      exact ⟨E.1,E.2.trans (by norm_num [cell12517])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy13 (n := 12517) (by norm_num)
        (q := 1 - (cell12517 ⟨13,by decide⟩).lower)
        (by norm_num [cell12517]) (by norm_num [cell12517])
      exact ⟨E.1,E.2.trans (by norm_num [cell12517])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy14 (n := 12517) (by norm_num)
        (q := 1 - (cell12517 ⟨14,by decide⟩).lower)
        (by norm_num [cell12517]) (by norm_num [cell12517])
      exact ⟨E.1,E.2.trans (by norm_num [cell12517])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy15 (n := 12517) (by norm_num)
        (q := 1 - (cell12517 ⟨15,by decide⟩).lower)
        (by norm_num [cell12517]) (by norm_num [cell12517])
      exact ⟨E.1,E.2.trans (by norm_num [cell12517])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy16 (n := 12517) (by norm_num)
        (q := 1 - (cell12517 ⟨16,by decide⟩).lower)
        (by norm_num [cell12517]) (by norm_num [cell12517])
      exact ⟨E.1,E.2.trans (by norm_num [cell12517])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy17 (n := 12517) (by norm_num)
        (q := 1 - (cell12517 ⟨17,by decide⟩).lower)
        (by norm_num [cell12517]) (by norm_num [cell12517])
      exact ⟨E.1,E.2.trans (by norm_num [cell12517])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy18 (n := 12517) (by norm_num)
        (q := 1 - (cell12517 ⟨18,by decide⟩).lower)
        (by norm_num [cell12517]) (by norm_num [cell12517])
      exact ⟨E.1,E.2.trans (by norm_num [cell12517])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy19 (n := 12517) (by norm_num)
        (q := 1 - (cell12517 ⟨19,by decide⟩).lower)
        (by norm_num [cell12517]) (by norm_num [cell12517])
      exact ⟨E.1,E.2.trans (by norm_num [cell12517])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy20 (n := 12517) (by norm_num)
        (q := 1 - (cell12517 ⟨20,by decide⟩).lower)
        (by norm_num [cell12517]) (by norm_num [cell12517])
      exact ⟨E.1,E.2.trans (by norm_num [cell12517])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy21 (n := 12517) (by norm_num)
        (q := 1 - (cell12517 ⟨21,by decide⟩).lower)
        (by norm_num [cell12517]) (by norm_num [cell12517])
      exact ⟨E.1,E.2.trans (by norm_num [cell12517])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy22 (n := 12517) (by norm_num)
        (q := 1 - (cell12517 ⟨22,by decide⟩).lower)
        (by norm_num [cell12517]) (by norm_num [cell12517])
      exact ⟨E.1,E.2.trans (by norm_num [cell12517])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy23 (n := 12517) (by norm_num)
        (q := 1 - (cell12517 ⟨23,by decide⟩).lower)
        (by norm_num [cell12517]) (by norm_num [cell12517])
      exact ⟨E.1,E.2.trans (by norm_num [cell12517])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy24 (n := 12517) (by norm_num)
        (q := 1 - (cell12517 ⟨24,by decide⟩).lower)
        (by norm_num [cell12517]) (by norm_num [cell12517])
      exact ⟨E.1,E.2.trans (by norm_num [cell12517])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy25 (n := 12517) (by norm_num)
        (q := 1 - (cell12517 ⟨25,by decide⟩).lower)
        (by norm_num [cell12517]) (by norm_num [cell12517])
      exact ⟨E.1,E.2.trans (by norm_num [cell12517])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy26 (n := 12517) (by norm_num)
        (q := 1 - (cell12517 ⟨26,by decide⟩).lower)
        (by norm_num [cell12517]) (by norm_num [cell12517])
      exact ⟨E.1,E.2.trans (by norm_num [cell12517])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy27 (n := 12517) (by norm_num)
        (q := 1 - (cell12517 ⟨27,by decide⟩).lower)
        (by norm_num [cell12517]) (by norm_num [cell12517])
      exact ⟨E.1,E.2.trans (by norm_num [cell12517])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy28 (n := 12517) (by norm_num)
        (q := 1 - (cell12517 ⟨28,by decide⟩).lower)
        (by norm_num [cell12517]) (by norm_num [cell12517])
      exact ⟨E.1,E.2.trans (by norm_num [cell12517])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy29 (n := 12517) (by norm_num)
        (q := 1 - (cell12517 ⟨29,by decide⟩).lower)
        (by norm_num [cell12517]) (by norm_num [cell12517])
      exact ⟨E.1,E.2.trans (by norm_num [cell12517])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy30 (n := 12517) (by norm_num)
        (q := 1 - (cell12517 ⟨30,by decide⟩).lower)
        (by norm_num [cell12517]) (by norm_num [cell12517])
      exact ⟨E.1,E.2.trans (by norm_num [cell12517])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy31 (n := 12517) (by norm_num)
        (q := 1 - (cell12517 ⟨31,by decide⟩).lower)
        (by norm_num [cell12517]) (by norm_num [cell12517])
      exact ⟨E.1,E.2.trans (by norm_num [cell12517])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy32 (n := 12517) (by norm_num)
        (q := 1 - (cell12517 ⟨32,by decide⟩).lower)
        (by norm_num [cell12517]) (by norm_num [cell12517])
      exact ⟨E.1,E.2.trans (by norm_num [cell12517])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy33 (n := 12517) (by norm_num)
        (q := 1 - (cell12517 ⟨33,by decide⟩).lower)
        (by norm_num [cell12517]) (by norm_num [cell12517])
      exact ⟨E.1,E.2.trans (by norm_num [cell12517])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy34 (n := 12517) (by norm_num)
        (q := 1 - (cell12517 ⟨34,by decide⟩).lower)
        (by norm_num [cell12517]) (by norm_num [cell12517])
      exact ⟨E.1,E.2.trans (by norm_num [cell12517])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy35 (n := 12517) (by norm_num)
        (q := 1 - (cell12517 ⟨35,by decide⟩).lower)
        (by norm_num [cell12517]) (by norm_num [cell12517])
      exact ⟨E.1,E.2.trans (by norm_num [cell12517])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy36 (n := 12517) (by norm_num)
        (q := 1 - (cell12517 ⟨36,by decide⟩).lower)
        (by norm_num [cell12517]) (by norm_num [cell12517])
      exact ⟨E.1,E.2.trans (by norm_num [cell12517])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy37 (n := 12517) (by norm_num)
        (q := 1 - (cell12517 ⟨37,by decide⟩).lower)
        (by norm_num [cell12517]) (by norm_num [cell12517])
      exact ⟨E.1,E.2.trans (by norm_num [cell12517])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy38 (n := 12517) (by norm_num)
        (q := 1 - (cell12517 ⟨38,by decide⟩).lower)
        (by norm_num [cell12517]) (by norm_num [cell12517])
      exact ⟨E.1,E.2.trans (by norm_num [cell12517])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy39 (n := 12517) (by norm_num)
        (q := 1 - (cell12517 ⟨39,by decide⟩).lower)
        (by norm_num [cell12517]) (by norm_num [cell12517])
      exact ⟨E.1,E.2.trans (by norm_num [cell12517])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy40 (n := 12517) (by norm_num)
        (q := 1 - (cell12517 ⟨40,by decide⟩).lower)
        (by norm_num [cell12517]) (by norm_num [cell12517])
      exact ⟨E.1,E.2.trans (by norm_num [cell12517])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy41 (n := 12517) (by norm_num)
        (q := 1 - (cell12517 ⟨41,by decide⟩).lower)
        (by norm_num [cell12517]) (by norm_num [cell12517])
      exact ⟨E.1,E.2.trans (by norm_num [cell12517])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy42 (n := 12517) (by norm_num)
        (q := 1 - (cell12517 ⟨42,by decide⟩).lower)
        (by norm_num [cell12517]) (by norm_num [cell12517])
      exact ⟨E.1,E.2.trans (by norm_num [cell12517])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy43 (n := 12517) (by norm_num)
        (q := 1 - (cell12517 ⟨43,by decide⟩).lower)
        (by norm_num [cell12517]) (by norm_num [cell12517])
      exact ⟨E.1,E.2.trans (by norm_num [cell12517])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy44 (n := 12517) (by norm_num)
        (q := 1 - (cell12517 ⟨44,by decide⟩).lower)
        (by norm_num [cell12517]) (by norm_num [cell12517])
      exact ⟨E.1,E.2.trans (by norm_num [cell12517])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy45 (n := 12517) (by norm_num)
        (q := 1 - (cell12517 ⟨45,by decide⟩).lower)
        (by norm_num [cell12517]) (by norm_num [cell12517])
      exact ⟨E.1,E.2.trans (by norm_num [cell12517])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy46 (n := 12517) (by norm_num)
        (q := 1 - (cell12517 ⟨46,by decide⟩).lower)
        (by norm_num [cell12517]) (by norm_num [cell12517])
      exact ⟨E.1,E.2.trans (by norm_num [cell12517])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy47 (n := 12517) (by norm_num)
        (q := 1 - (cell12517 ⟨47,by decide⟩).lower)
        (by norm_num [cell12517]) (by norm_num [cell12517])
      exact ⟨E.1,E.2.trans (by norm_num [cell12517])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy48 (n := 12517) (by norm_num)
        (q := 1 - (cell12517 ⟨48,by decide⟩).lower)
        (by norm_num [cell12517]) (by norm_num [cell12517])
      exact ⟨E.1,E.2.trans (by norm_num [cell12517])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy49 (n := 12517) (by norm_num)
        (q := 1 - (cell12517 ⟨49,by decide⟩).lower)
        (by norm_num [cell12517]) (by norm_num [cell12517])
      exact ⟨E.1,E.2.trans (by norm_num [cell12517])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy50 (n := 12517) (by norm_num)
        (q := 1 - (cell12517 ⟨50,by decide⟩).lower)
        (by norm_num [cell12517]) (by norm_num [cell12517])
      exact ⟨E.1,E.2.trans (by norm_num [cell12517])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy51 (n := 12517) (by norm_num)
        (q := 1 - (cell12517 ⟨51,by decide⟩).lower)
        (by norm_num [cell12517]) (by norm_num [cell12517])
      exact ⟨E.1,E.2.trans (by norm_num [cell12517])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy52 (n := 12517) (by norm_num)
        (q := 1 - (cell12517 ⟨52,by decide⟩).lower)
        (by norm_num [cell12517]) (by norm_num [cell12517])
      exact ⟨E.1,E.2.trans (by norm_num [cell12517])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12517

/-! Source-cell containment and simple scalar guards at 12517. -/
namespace BstLean.Part269.N12517
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12517)
open BstLean.Part268 (cell12517)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12517 ⟨10,by decide⟩).lower ∧ (cell12517 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12517 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12517 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12517 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12517 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12517 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12517,cell12517,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12517 ⟨11,by decide⟩).lower ∧ (cell12517 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12517 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12517 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12517 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12517 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12517 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12517,cell12517,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12517 ⟨12,by decide⟩).lower ∧ (cell12517 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12517 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12517 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12517 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12517 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12517 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12517,cell12517,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12517 ⟨13,by decide⟩).lower ∧ (cell12517 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12517 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12517 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12517 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12517 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12517 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12517,cell12517,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12517 ⟨14,by decide⟩).lower ∧ (cell12517 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12517 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12517 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12517 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12517 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12517 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12517,cell12517,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12517 ⟨15,by decide⟩).lower ∧ (cell12517 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12517 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12517 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12517 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12517 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12517 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12517,cell12517,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12517 ⟨16,by decide⟩).lower ∧ (cell12517 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12517 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12517 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12517 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12517 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12517 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12517,cell12517,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12517 ⟨17,by decide⟩).lower ∧ (cell12517 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12517 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12517 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12517 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12517 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12517 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12517,cell12517,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12517 ⟨18,by decide⟩).lower ∧ (cell12517 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12517 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12517 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12517 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12517 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12517 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12517,cell12517,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12517 ⟨19,by decide⟩).lower ∧ (cell12517 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12517 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12517 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12517 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12517 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12517 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12517,cell12517,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12517 ⟨20,by decide⟩).lower ∧ (cell12517 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12517 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12517 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12517 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12517 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12517 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12517,cell12517,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12517 ⟨21,by decide⟩).lower ∧ (cell12517 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12517 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12517 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12517 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12517 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12517 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12517,cell12517,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12517 ⟨22,by decide⟩).lower ∧ (cell12517 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12517 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12517 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12517 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12517 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12517 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12517,cell12517,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12517 ⟨23,by decide⟩).lower ∧ (cell12517 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12517 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12517 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12517 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12517 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12517 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12517,cell12517,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12517 ⟨24,by decide⟩).lower ∧ (cell12517 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12517 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12517 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12517 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12517 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12517 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12517,cell12517,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12517 ⟨25,by decide⟩).lower ∧ (cell12517 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12517 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12517 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12517 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12517 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12517 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12517,cell12517,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12517 ⟨26,by decide⟩).lower ∧ (cell12517 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12517 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12517 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12517 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12517 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12517 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12517,cell12517,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12517 ⟨27,by decide⟩).lower ∧ (cell12517 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12517 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12517 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12517 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12517 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12517 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12517,cell12517,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12517 ⟨28,by decide⟩).lower ∧ (cell12517 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12517 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12517 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12517 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12517 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12517 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12517,cell12517,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12517 ⟨29,by decide⟩).lower ∧ (cell12517 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12517 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12517 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12517 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12517 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12517 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12517,cell12517,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12517 ⟨30,by decide⟩).lower ∧ (cell12517 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12517 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12517 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12517 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12517 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12517 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12517,cell12517,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12517 ⟨31,by decide⟩).lower ∧ (cell12517 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12517 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12517 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12517 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12517 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12517 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12517,cell12517,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12517 ⟨32,by decide⟩).lower ∧ (cell12517 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12517 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12517 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12517 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12517 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12517 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12517,cell12517,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12517 ⟨33,by decide⟩).lower ∧ (cell12517 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12517 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12517 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12517 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12517 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12517 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12517,cell12517,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12517 ⟨34,by decide⟩).lower ∧ (cell12517 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12517 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12517 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12517 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12517 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12517 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12517,cell12517,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12517 ⟨35,by decide⟩).lower ∧ (cell12517 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12517 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12517 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12517 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12517 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12517 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12517,cell12517,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12517 ⟨36,by decide⟩).lower ∧ (cell12517 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12517 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12517 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12517 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12517 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12517 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12517,cell12517,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12517 ⟨37,by decide⟩).lower ∧ (cell12517 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12517 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12517 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12517 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12517 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12517 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12517,cell12517,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12517 ⟨38,by decide⟩).lower ∧ (cell12517 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12517 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12517 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12517 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12517 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12517 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12517,cell12517,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12517 ⟨39,by decide⟩).lower ∧ (cell12517 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12517 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12517 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12517 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12517 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12517 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12517,cell12517,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12517 ⟨40,by decide⟩).lower ∧ (cell12517 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12517 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12517 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12517 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12517 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12517 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12517,cell12517,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12517 ⟨41,by decide⟩).lower ∧ (cell12517 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12517 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12517 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12517 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12517 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12517 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12517,cell12517,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12517 ⟨42,by decide⟩).lower ∧ (cell12517 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12517 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12517 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12517 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12517 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12517 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12517,cell12517,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12517 ⟨43,by decide⟩).lower ∧ (cell12517 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12517 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12517 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12517 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12517 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12517 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12517,cell12517,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12517 ⟨44,by decide⟩).lower ∧ (cell12517 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12517 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12517 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12517 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12517 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12517 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12517,cell12517,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12517 ⟨45,by decide⟩).lower ∧ (cell12517 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12517 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12517 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12517 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12517 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12517 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12517,cell12517,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12517 ⟨46,by decide⟩).lower ∧ (cell12517 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12517 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12517 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12517 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12517 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12517 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12517,cell12517,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12517 ⟨47,by decide⟩).lower ∧ (cell12517 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12517 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12517 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12517 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12517 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12517 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12517,cell12517,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12517 ⟨48,by decide⟩).lower ∧ (cell12517 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12517 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12517 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12517 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12517 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12517 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12517,cell12517,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12517 ⟨49,by decide⟩).lower ∧ (cell12517 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12517 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12517 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12517 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12517 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12517 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12517,cell12517,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12517 ⟨50,by decide⟩).lower ∧ (cell12517 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12517 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12517 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12517 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12517 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12517 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12517,cell12517,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12517 ⟨51,by decide⟩).lower ∧ (cell12517 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12517 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12517 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12517 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12517 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12517 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12517,cell12517,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12517 ⟨52,by decide⟩).lower ∧ (cell12517 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12517 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12517 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12517 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12517 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12517 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12517,cell12517,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12517 i).lower ∧
    (cell12517 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12517 i).upper ≤ (0.532 : ℝ) ∧
    (cell12517 i).centre ≤ (0.1 : ℝ) ∧ (cell12517 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12517 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12517 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12517

/-! The local source numeric instances at 12517 have no network premises. -/
namespace BstLean.Part269.N12517
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12517)
open BstLean.Part268 (cell12517)

noncomputable def sourceNumerics12517 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12517 (cell12517 i)
      scalarRow12517.M scalarRow12517.H scalarRow12517.xi := by
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
    energy_allowance := scalarRow12517.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12517]
    centre_nonneg := (scalarRow12517.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D6.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12517])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12517
/-! Actual 12518 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12518
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12518 ≤ (1.036070895787 : ℝ) := by
  have hr : (111.883868363584 : ℝ) ≤ √(12518 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.883868363584 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12518 12518 (11 / 1000) ≤
    (0.008543564828 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12518) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.883868363584 : ℝ) ≤ √(12518 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12518)
  have hdiv : K / √(12518 : ℝ) ≤ K / 111.883868363584 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.883868363584 ≤ (0.008543564828 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12518.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12518 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12518 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12518 := gPlus_lower 12518
end BstLean.Part269.N12518

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12518
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036070895786 : ℝ) ≤ wn 12518 := by
  have hn : √(12518 : ℝ) ≤ 111.883868363585 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12518 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.883868363585 ≤ 2 / √(12518 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000255607538 : ℝ) ≤ rhoBar 12518 BstLean.Part154.csC ∧
    rhoBar 12518 BstLean.Part154.csC ≤ 0.000255607934 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036070895786 : ℝ) / (1.295212 * 12518) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036070895787 : ℝ) / (1.29521 * 12518) := by gcongr
      _ ≤ (0.000255607934 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12518 BstLean.Part154.csC) ≤ 0.001022497072 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12518 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12518 BstLean.Part154.csC) (piBar (rhoBar 12518 BstLean.Part154.csC)) ≤ 0.000195235199 ∧
    cc1 (rhoBar 12518 BstLean.Part154.csC) (piBar (rhoBar 12518 BstLean.Part154.csC)) ≤ 0.000124229426 ∧
    cc2 (rhoBar 12518 BstLean.Part154.csC) ≤ 0.000072116100 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12518 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12518 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12518 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12518 BstLean.Part154.csC * nuR (rhoBar 12518 BstLean.Part154.csC)) ≤ 0.000511232202 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000255607934 : ℝ) * 0.001022497072 := by gcongr
      _ ≤ (0.000511232202 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12518 BstLean.Part154.csC) * nuR (rhoBar 12518 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001022497072 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12518 BstLean.Part154.csC) * rhoBar 12518 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000255607934 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000255607934 / 2 + 0.399 * 0.001022497072 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000195235199 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000511232202 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124229426 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000255607934 / 1.414213562 := by gcongr
      _ ≤ (0.000072116100 : ℝ) := by norm_num

end BstLean.Part269.N12518

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12518
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12518 BstLean.Part154.csC) (piBar (rhoBar 12518 BstLean.Part154.csC)) ≤ 1.64608E-7 := by
  have hr0 : 0 ≤ rhoBar 12518 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12518 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12518 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12518 BstLean.Part154.csC) (piBar (rhoBar 12518 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12518 BstLean.Part154.csC) (piBar (rhoBar 12518 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12518 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000195235199 : ℝ) ^ 2 + 0.000124229426 ^ 2 + 3 * 0.000072116100 ^ 2 +
        2 * 0.797885 * 0.000195235199 * 0.000124229426 + 2 * 0.000195235199 * 0.000072116100 +
        4 * 0.797885 * 0.000124229426 * 0.000072116100 := by gcongr
    _ ≤ (1.64608E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12518 BstLean.Part154.csC Θ ≤ 0.002668865862 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12518 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12518 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12518 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12518 BstLean.Part154.csC) (piBar (rhoBar 12518 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12518 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036070895787 * 1.64608E-7 / (0.000255607538 : ℝ) := by gcongr
    _ ≤ 0.002668865862 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12518 BstLean.Part154.csC Θ ≤ 0.002961999852 + 0.000674378955 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12518 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12518 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12518 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036070895787 : ℝ) * ((2 * Θ * 0.000255607934 +
        (6863 / 10000) * 0.000255607934 * 12518 * 0.001022497072) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002961999852 + 0.000674378955 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12518 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12518 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12518 0.011 Θ ∧ gammaRatio 12518 0.011 Θ ≤ 0.000087871398 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12518 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036070895787 : ℝ) * 0.525 / ((1 - 0.011) * 12518) := by gcongr
      _ ≤ (0.000087871398 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12518 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12518 0.011 Θ) :=
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
    badAllowance 12518 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000774418828 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12518 BstLean.Part154.csC) 1.22 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 2 (rhoBar 12518 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12518 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12518 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12518 0.011 Θ) 1.12 ≤ 3.3895E-8 := by
    have he : (17.2 : ℝ) ≤ gap 1 (gammaRatio 12518 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12518 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12518 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12518 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12518 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036070895787 : ℝ) * 12518 *
        (2.7751E-8 / 1.1045361 + 3.3895E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000774418828 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12518 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003736418680 + 0.003343244817 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12518

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12518
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12518 BstLean.Part154.csC) (piBar (rhoBar 12518 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12518 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12518 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12518 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12518 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12518 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12518 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12518 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12518 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12518 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12518 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12518 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12518 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12518 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12518 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052868624483 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12518) ≤ 0.010673903205 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12518 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036070895787)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010673903205 + 2 * 0.737676 / 12518) := by gcongr
    _ ≤ (0.052868624483 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12518 12 ≤ 0.0015 := by
  exact BstLean.Part269.S6.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12518

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12518
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560495218046 : ℝ) ≤ plow 12518 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12518) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052998222209)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001401154578) : eMP 12518 0.011 xi bn ≤ 0.001206014523 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12518 : ℝ) * (1 - 0.011))) ≤ 0.000596282916 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001401154578 / (12518 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000596282916 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000596282916 : ℝ) + 3.141593 * 0.052998222209 / (12518 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001206014523 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052998222209)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001401154578) : PiBarMP 12518 12 0.011 xi bn ≤ 0.162431110269 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12518 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037431999386 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.266805472252 : ℝ) ≤ √((12518 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.883868363584 : ℝ) ≤ √(12518 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12518) ≤ 0.124525621670 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037431999386 + 0.052998222209 * 1.772454 / (2 * (111.266805472252 : ℝ))) * (1 + 0.001206014523) +
        8 / (12518 * 111.883868363584) + 0.124525621670 := by gcongr
    _ ≤ (0.162431110269 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052998222209)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001401154578) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283082052000) :
    parallelOracle 12518 0.011 xi bn cd ≤ 0.163436659860 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12518 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12518 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560495218046 : ℝ) ≤ plow 12518 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.883868363584 : ℝ) ≤ √(12518 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.283082052000 : ℝ) / (2 * 0.560495218046 * 111.883868363584)) * 0.162431110269 +
        0.283082052000 ^ 2 / (2 * 0.560495218046 * 111.883868363584) := by gcongr
    _ ≤ (0.163436659860 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052998222209) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001401154578)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283082052000) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12518 12518 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560495218046 : ℝ) ≤ plow 12518 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.883868363584 : ℝ) ≤ √(12518 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12518 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12518 Θ 1.22 ≤ 0.011852472742 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.883868363584 := by gcongr <;> linarith
      _ ≤ (0.011852472742 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12518 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12518 12518 0.011 ≤ 0.008543564828 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12518 12518 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12518 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12518 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12518 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12518 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163436659860 + 0.011852472742 + (0.008543564828 : ℝ) *
        (1 + 2 * (0.283082052000 + 0.011852472742) / (0.560495218046 * 111.883868363584))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12518]

end BstLean.Part269.N12518

/-! The original eight local profiles supply actual 12518 moment certificates. -/
namespace BstLean.Part269.N12518
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12518 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12518 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12518 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052998222209 ∧
    0 ≤ bN 12518 BstLean.Part154.csC (groupTheta g) ∧ bN 12518 BstLean.Part154.csC (groupTheta g) ≤ 0.001401154578 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12518 12518 0.011
      (momentAllowance 12518 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12518 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12518 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12518 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12518 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12518 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230213427517 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12518 0.011
      (momentAllowance 12518 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12518 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12518
/-! The actual computed-centre upper energy formula at 12518. -/
namespace BstLean.Part269.N12518
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12518

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12518
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12518)
open BstLean.Part268 (cell12518)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086040145284
  | 2 => 0.086993444438
  | 3 => 0.087946493214
  | 4 => 0.088901075170
  | 5 => 0.089859334610
  | 6 => 0.090823828452
  | 7 => 0.091797582647
  | 8 => 0.092784153176
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12518 12518 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12518 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003740909217 + 0.003348232271 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S6.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12518

/-! Actual upper energy certificates on all 43 source endpoints at 12518. -/
namespace BstLean.Part269.N12518
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12518)
open BstLean.Part268 (cell12518)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12518 (gMinus 12518) (1 - (cell12518 i).lower) ≤ 1 ∧
    energyUpper 12518 (gMinus 12518) (BstLean.Part211.gPlus 12518)
      (finiteEnergy 12518 12518 0.011) (1 - (cell12518 i).lower) ≤
      (cell12518 i).energy := by
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
      have E := BstLean.Part269.S6.uniformEnergy10 (n := 12518) (by norm_num)
        (q := 1 - (cell12518 ⟨10,by decide⟩).lower)
        (by norm_num [cell12518]) (by norm_num [cell12518])
      exact ⟨E.1,E.2.trans (by norm_num [cell12518])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy11 (n := 12518) (by norm_num)
        (q := 1 - (cell12518 ⟨11,by decide⟩).lower)
        (by norm_num [cell12518]) (by norm_num [cell12518])
      exact ⟨E.1,E.2.trans (by norm_num [cell12518])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy12 (n := 12518) (by norm_num)
        (q := 1 - (cell12518 ⟨12,by decide⟩).lower)
        (by norm_num [cell12518]) (by norm_num [cell12518])
      exact ⟨E.1,E.2.trans (by norm_num [cell12518])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy13 (n := 12518) (by norm_num)
        (q := 1 - (cell12518 ⟨13,by decide⟩).lower)
        (by norm_num [cell12518]) (by norm_num [cell12518])
      exact ⟨E.1,E.2.trans (by norm_num [cell12518])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy14 (n := 12518) (by norm_num)
        (q := 1 - (cell12518 ⟨14,by decide⟩).lower)
        (by norm_num [cell12518]) (by norm_num [cell12518])
      exact ⟨E.1,E.2.trans (by norm_num [cell12518])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy15 (n := 12518) (by norm_num)
        (q := 1 - (cell12518 ⟨15,by decide⟩).lower)
        (by norm_num [cell12518]) (by norm_num [cell12518])
      exact ⟨E.1,E.2.trans (by norm_num [cell12518])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy16 (n := 12518) (by norm_num)
        (q := 1 - (cell12518 ⟨16,by decide⟩).lower)
        (by norm_num [cell12518]) (by norm_num [cell12518])
      exact ⟨E.1,E.2.trans (by norm_num [cell12518])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy17 (n := 12518) (by norm_num)
        (q := 1 - (cell12518 ⟨17,by decide⟩).lower)
        (by norm_num [cell12518]) (by norm_num [cell12518])
      exact ⟨E.1,E.2.trans (by norm_num [cell12518])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy18 (n := 12518) (by norm_num)
        (q := 1 - (cell12518 ⟨18,by decide⟩).lower)
        (by norm_num [cell12518]) (by norm_num [cell12518])
      exact ⟨E.1,E.2.trans (by norm_num [cell12518])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy19 (n := 12518) (by norm_num)
        (q := 1 - (cell12518 ⟨19,by decide⟩).lower)
        (by norm_num [cell12518]) (by norm_num [cell12518])
      exact ⟨E.1,E.2.trans (by norm_num [cell12518])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy20 (n := 12518) (by norm_num)
        (q := 1 - (cell12518 ⟨20,by decide⟩).lower)
        (by norm_num [cell12518]) (by norm_num [cell12518])
      exact ⟨E.1,E.2.trans (by norm_num [cell12518])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy21 (n := 12518) (by norm_num)
        (q := 1 - (cell12518 ⟨21,by decide⟩).lower)
        (by norm_num [cell12518]) (by norm_num [cell12518])
      exact ⟨E.1,E.2.trans (by norm_num [cell12518])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy22 (n := 12518) (by norm_num)
        (q := 1 - (cell12518 ⟨22,by decide⟩).lower)
        (by norm_num [cell12518]) (by norm_num [cell12518])
      exact ⟨E.1,E.2.trans (by norm_num [cell12518])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy23 (n := 12518) (by norm_num)
        (q := 1 - (cell12518 ⟨23,by decide⟩).lower)
        (by norm_num [cell12518]) (by norm_num [cell12518])
      exact ⟨E.1,E.2.trans (by norm_num [cell12518])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy24 (n := 12518) (by norm_num)
        (q := 1 - (cell12518 ⟨24,by decide⟩).lower)
        (by norm_num [cell12518]) (by norm_num [cell12518])
      exact ⟨E.1,E.2.trans (by norm_num [cell12518])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy25 (n := 12518) (by norm_num)
        (q := 1 - (cell12518 ⟨25,by decide⟩).lower)
        (by norm_num [cell12518]) (by norm_num [cell12518])
      exact ⟨E.1,E.2.trans (by norm_num [cell12518])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy26 (n := 12518) (by norm_num)
        (q := 1 - (cell12518 ⟨26,by decide⟩).lower)
        (by norm_num [cell12518]) (by norm_num [cell12518])
      exact ⟨E.1,E.2.trans (by norm_num [cell12518])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy27 (n := 12518) (by norm_num)
        (q := 1 - (cell12518 ⟨27,by decide⟩).lower)
        (by norm_num [cell12518]) (by norm_num [cell12518])
      exact ⟨E.1,E.2.trans (by norm_num [cell12518])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy28 (n := 12518) (by norm_num)
        (q := 1 - (cell12518 ⟨28,by decide⟩).lower)
        (by norm_num [cell12518]) (by norm_num [cell12518])
      exact ⟨E.1,E.2.trans (by norm_num [cell12518])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy29 (n := 12518) (by norm_num)
        (q := 1 - (cell12518 ⟨29,by decide⟩).lower)
        (by norm_num [cell12518]) (by norm_num [cell12518])
      exact ⟨E.1,E.2.trans (by norm_num [cell12518])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy30 (n := 12518) (by norm_num)
        (q := 1 - (cell12518 ⟨30,by decide⟩).lower)
        (by norm_num [cell12518]) (by norm_num [cell12518])
      exact ⟨E.1,E.2.trans (by norm_num [cell12518])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy31 (n := 12518) (by norm_num)
        (q := 1 - (cell12518 ⟨31,by decide⟩).lower)
        (by norm_num [cell12518]) (by norm_num [cell12518])
      exact ⟨E.1,E.2.trans (by norm_num [cell12518])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy32 (n := 12518) (by norm_num)
        (q := 1 - (cell12518 ⟨32,by decide⟩).lower)
        (by norm_num [cell12518]) (by norm_num [cell12518])
      exact ⟨E.1,E.2.trans (by norm_num [cell12518])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy33 (n := 12518) (by norm_num)
        (q := 1 - (cell12518 ⟨33,by decide⟩).lower)
        (by norm_num [cell12518]) (by norm_num [cell12518])
      exact ⟨E.1,E.2.trans (by norm_num [cell12518])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy34 (n := 12518) (by norm_num)
        (q := 1 - (cell12518 ⟨34,by decide⟩).lower)
        (by norm_num [cell12518]) (by norm_num [cell12518])
      exact ⟨E.1,E.2.trans (by norm_num [cell12518])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy35 (n := 12518) (by norm_num)
        (q := 1 - (cell12518 ⟨35,by decide⟩).lower)
        (by norm_num [cell12518]) (by norm_num [cell12518])
      exact ⟨E.1,E.2.trans (by norm_num [cell12518])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy36 (n := 12518) (by norm_num)
        (q := 1 - (cell12518 ⟨36,by decide⟩).lower)
        (by norm_num [cell12518]) (by norm_num [cell12518])
      exact ⟨E.1,E.2.trans (by norm_num [cell12518])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy37 (n := 12518) (by norm_num)
        (q := 1 - (cell12518 ⟨37,by decide⟩).lower)
        (by norm_num [cell12518]) (by norm_num [cell12518])
      exact ⟨E.1,E.2.trans (by norm_num [cell12518])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy38 (n := 12518) (by norm_num)
        (q := 1 - (cell12518 ⟨38,by decide⟩).lower)
        (by norm_num [cell12518]) (by norm_num [cell12518])
      exact ⟨E.1,E.2.trans (by norm_num [cell12518])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy39 (n := 12518) (by norm_num)
        (q := 1 - (cell12518 ⟨39,by decide⟩).lower)
        (by norm_num [cell12518]) (by norm_num [cell12518])
      exact ⟨E.1,E.2.trans (by norm_num [cell12518])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy40 (n := 12518) (by norm_num)
        (q := 1 - (cell12518 ⟨40,by decide⟩).lower)
        (by norm_num [cell12518]) (by norm_num [cell12518])
      exact ⟨E.1,E.2.trans (by norm_num [cell12518])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy41 (n := 12518) (by norm_num)
        (q := 1 - (cell12518 ⟨41,by decide⟩).lower)
        (by norm_num [cell12518]) (by norm_num [cell12518])
      exact ⟨E.1,E.2.trans (by norm_num [cell12518])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy42 (n := 12518) (by norm_num)
        (q := 1 - (cell12518 ⟨42,by decide⟩).lower)
        (by norm_num [cell12518]) (by norm_num [cell12518])
      exact ⟨E.1,E.2.trans (by norm_num [cell12518])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy43 (n := 12518) (by norm_num)
        (q := 1 - (cell12518 ⟨43,by decide⟩).lower)
        (by norm_num [cell12518]) (by norm_num [cell12518])
      exact ⟨E.1,E.2.trans (by norm_num [cell12518])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy44 (n := 12518) (by norm_num)
        (q := 1 - (cell12518 ⟨44,by decide⟩).lower)
        (by norm_num [cell12518]) (by norm_num [cell12518])
      exact ⟨E.1,E.2.trans (by norm_num [cell12518])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy45 (n := 12518) (by norm_num)
        (q := 1 - (cell12518 ⟨45,by decide⟩).lower)
        (by norm_num [cell12518]) (by norm_num [cell12518])
      exact ⟨E.1,E.2.trans (by norm_num [cell12518])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy46 (n := 12518) (by norm_num)
        (q := 1 - (cell12518 ⟨46,by decide⟩).lower)
        (by norm_num [cell12518]) (by norm_num [cell12518])
      exact ⟨E.1,E.2.trans (by norm_num [cell12518])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy47 (n := 12518) (by norm_num)
        (q := 1 - (cell12518 ⟨47,by decide⟩).lower)
        (by norm_num [cell12518]) (by norm_num [cell12518])
      exact ⟨E.1,E.2.trans (by norm_num [cell12518])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy48 (n := 12518) (by norm_num)
        (q := 1 - (cell12518 ⟨48,by decide⟩).lower)
        (by norm_num [cell12518]) (by norm_num [cell12518])
      exact ⟨E.1,E.2.trans (by norm_num [cell12518])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy49 (n := 12518) (by norm_num)
        (q := 1 - (cell12518 ⟨49,by decide⟩).lower)
        (by norm_num [cell12518]) (by norm_num [cell12518])
      exact ⟨E.1,E.2.trans (by norm_num [cell12518])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy50 (n := 12518) (by norm_num)
        (q := 1 - (cell12518 ⟨50,by decide⟩).lower)
        (by norm_num [cell12518]) (by norm_num [cell12518])
      exact ⟨E.1,E.2.trans (by norm_num [cell12518])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy51 (n := 12518) (by norm_num)
        (q := 1 - (cell12518 ⟨51,by decide⟩).lower)
        (by norm_num [cell12518]) (by norm_num [cell12518])
      exact ⟨E.1,E.2.trans (by norm_num [cell12518])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy52 (n := 12518) (by norm_num)
        (q := 1 - (cell12518 ⟨52,by decide⟩).lower)
        (by norm_num [cell12518]) (by norm_num [cell12518])
      exact ⟨E.1,E.2.trans (by norm_num [cell12518])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12518

/-! Source-cell containment and simple scalar guards at 12518. -/
namespace BstLean.Part269.N12518
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12518)
open BstLean.Part268 (cell12518)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12518 ⟨10,by decide⟩).lower ∧ (cell12518 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12518 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12518 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12518 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12518 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12518 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12518,cell12518,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12518 ⟨11,by decide⟩).lower ∧ (cell12518 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12518 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12518 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12518 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12518 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12518 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12518,cell12518,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12518 ⟨12,by decide⟩).lower ∧ (cell12518 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12518 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12518 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12518 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12518 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12518 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12518,cell12518,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12518 ⟨13,by decide⟩).lower ∧ (cell12518 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12518 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12518 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12518 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12518 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12518 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12518,cell12518,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12518 ⟨14,by decide⟩).lower ∧ (cell12518 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12518 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12518 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12518 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12518 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12518 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12518,cell12518,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12518 ⟨15,by decide⟩).lower ∧ (cell12518 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12518 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12518 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12518 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12518 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12518 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12518,cell12518,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12518 ⟨16,by decide⟩).lower ∧ (cell12518 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12518 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12518 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12518 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12518 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12518 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12518,cell12518,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12518 ⟨17,by decide⟩).lower ∧ (cell12518 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12518 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12518 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12518 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12518 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12518 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12518,cell12518,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12518 ⟨18,by decide⟩).lower ∧ (cell12518 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12518 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12518 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12518 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12518 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12518 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12518,cell12518,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12518 ⟨19,by decide⟩).lower ∧ (cell12518 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12518 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12518 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12518 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12518 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12518 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12518,cell12518,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12518 ⟨20,by decide⟩).lower ∧ (cell12518 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12518 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12518 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12518 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12518 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12518 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12518,cell12518,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12518 ⟨21,by decide⟩).lower ∧ (cell12518 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12518 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12518 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12518 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12518 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12518 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12518,cell12518,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12518 ⟨22,by decide⟩).lower ∧ (cell12518 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12518 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12518 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12518 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12518 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12518 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12518,cell12518,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12518 ⟨23,by decide⟩).lower ∧ (cell12518 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12518 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12518 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12518 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12518 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12518 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12518,cell12518,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12518 ⟨24,by decide⟩).lower ∧ (cell12518 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12518 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12518 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12518 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12518 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12518 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12518,cell12518,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12518 ⟨25,by decide⟩).lower ∧ (cell12518 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12518 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12518 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12518 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12518 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12518 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12518,cell12518,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12518 ⟨26,by decide⟩).lower ∧ (cell12518 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12518 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12518 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12518 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12518 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12518 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12518,cell12518,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12518 ⟨27,by decide⟩).lower ∧ (cell12518 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12518 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12518 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12518 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12518 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12518 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12518,cell12518,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12518 ⟨28,by decide⟩).lower ∧ (cell12518 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12518 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12518 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12518 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12518 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12518 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12518,cell12518,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12518 ⟨29,by decide⟩).lower ∧ (cell12518 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12518 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12518 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12518 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12518 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12518 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12518,cell12518,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12518 ⟨30,by decide⟩).lower ∧ (cell12518 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12518 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12518 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12518 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12518 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12518 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12518,cell12518,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12518 ⟨31,by decide⟩).lower ∧ (cell12518 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12518 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12518 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12518 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12518 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12518 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12518,cell12518,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12518 ⟨32,by decide⟩).lower ∧ (cell12518 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12518 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12518 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12518 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12518 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12518 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12518,cell12518,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12518 ⟨33,by decide⟩).lower ∧ (cell12518 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12518 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12518 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12518 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12518 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12518 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12518,cell12518,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12518 ⟨34,by decide⟩).lower ∧ (cell12518 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12518 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12518 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12518 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12518 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12518 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12518,cell12518,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12518 ⟨35,by decide⟩).lower ∧ (cell12518 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12518 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12518 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12518 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12518 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12518 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12518,cell12518,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12518 ⟨36,by decide⟩).lower ∧ (cell12518 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12518 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12518 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12518 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12518 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12518 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12518,cell12518,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12518 ⟨37,by decide⟩).lower ∧ (cell12518 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12518 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12518 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12518 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12518 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12518 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12518,cell12518,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12518 ⟨38,by decide⟩).lower ∧ (cell12518 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12518 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12518 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12518 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12518 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12518 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12518,cell12518,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12518 ⟨39,by decide⟩).lower ∧ (cell12518 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12518 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12518 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12518 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12518 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12518 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12518,cell12518,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12518 ⟨40,by decide⟩).lower ∧ (cell12518 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12518 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12518 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12518 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12518 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12518 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12518,cell12518,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12518 ⟨41,by decide⟩).lower ∧ (cell12518 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12518 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12518 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12518 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12518 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12518 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12518,cell12518,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12518 ⟨42,by decide⟩).lower ∧ (cell12518 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12518 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12518 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12518 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12518 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12518 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12518,cell12518,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12518 ⟨43,by decide⟩).lower ∧ (cell12518 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12518 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12518 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12518 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12518 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12518 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12518,cell12518,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12518 ⟨44,by decide⟩).lower ∧ (cell12518 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12518 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12518 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12518 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12518 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12518 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12518,cell12518,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12518 ⟨45,by decide⟩).lower ∧ (cell12518 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12518 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12518 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12518 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12518 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12518 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12518,cell12518,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12518 ⟨46,by decide⟩).lower ∧ (cell12518 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12518 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12518 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12518 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12518 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12518 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12518,cell12518,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12518 ⟨47,by decide⟩).lower ∧ (cell12518 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12518 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12518 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12518 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12518 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12518 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12518,cell12518,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12518 ⟨48,by decide⟩).lower ∧ (cell12518 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12518 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12518 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12518 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12518 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12518 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12518,cell12518,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12518 ⟨49,by decide⟩).lower ∧ (cell12518 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12518 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12518 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12518 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12518 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12518 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12518,cell12518,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12518 ⟨50,by decide⟩).lower ∧ (cell12518 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12518 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12518 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12518 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12518 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12518 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12518,cell12518,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12518 ⟨51,by decide⟩).lower ∧ (cell12518 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12518 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12518 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12518 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12518 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12518 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12518,cell12518,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12518 ⟨52,by decide⟩).lower ∧ (cell12518 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12518 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12518 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12518 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12518 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12518 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12518,cell12518,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12518 i).lower ∧
    (cell12518 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12518 i).upper ≤ (0.532 : ℝ) ∧
    (cell12518 i).centre ≤ (0.1 : ℝ) ∧ (cell12518 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12518 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12518 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12518

/-! The local source numeric instances at 12518 have no network premises. -/
namespace BstLean.Part269.N12518
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12518)
open BstLean.Part268 (cell12518)

noncomputable def sourceNumerics12518 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12518 (cell12518 i)
      scalarRow12518.M scalarRow12518.H scalarRow12518.xi := by
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
    energy_allowance := scalarRow12518.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12518]
    centre_nonneg := (scalarRow12518.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D6.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12518])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12518
/-! Actual 12519 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12519
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12519 ≤ (1.036069442350 : ℝ) := by
  have hr : (111.888337193829 : ℝ) ≤ √(12519 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.888337193829 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12519 12519 (11 / 1000) ≤
    (0.008543223594 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12519) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.888337193829 : ℝ) ≤ √(12519 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12519)
  have hdiv : K / √(12519 : ℝ) ≤ K / 111.888337193829 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.888337193829 ≤ (0.008543223594 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12519.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12519 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12519 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12519 := gPlus_lower 12519
end BstLean.Part269.N12519

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12519
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036069442349 : ℝ) ≤ wn 12519 := by
  have hn : √(12519 : ℝ) ≤ 111.888337193830 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12519 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.888337193830 ≤ 2 / √(12519 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000255586762 : ℝ) ≤ rhoBar 12519 BstLean.Part154.csC ∧
    rhoBar 12519 BstLean.Part154.csC ≤ 0.000255587158 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036069442349 : ℝ) / (1.295212 * 12519) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036069442350 : ℝ) / (1.29521 * 12519) := by gcongr
      _ ≤ (0.000255587158 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12519 BstLean.Part154.csC) ≤ 0.001022413957 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12519 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12519 BstLean.Part154.csC) (piBar (rhoBar 12519 BstLean.Part154.csC)) ≤ 0.000195219329 ∧
    cc1 (rhoBar 12519 BstLean.Part154.csC) (piBar (rhoBar 12519 BstLean.Part154.csC)) ≤ 0.000124219328 ∧
    cc2 (rhoBar 12519 BstLean.Part154.csC) ≤ 0.000072110238 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12519 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12519 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12519 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12519 BstLean.Part154.csC * nuR (rhoBar 12519 BstLean.Part154.csC)) ≤ 0.000511190647 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000255587158 : ℝ) * 0.001022413957 := by gcongr
      _ ≤ (0.000511190647 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12519 BstLean.Part154.csC) * nuR (rhoBar 12519 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001022413957 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12519 BstLean.Part154.csC) * rhoBar 12519 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000255587158 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000255587158 / 2 + 0.399 * 0.001022413957 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000195219329 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000511190647 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124219328 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000255587158 / 1.414213562 := by gcongr
      _ ≤ (0.000072110238 : ℝ) := by norm_num

end BstLean.Part269.N12519

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12519
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12519 BstLean.Part154.csC) (piBar (rhoBar 12519 BstLean.Part154.csC)) ≤ 1.64581E-7 := by
  have hr0 : 0 ≤ rhoBar 12519 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12519 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12519 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12519 BstLean.Part154.csC) (piBar (rhoBar 12519 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12519 BstLean.Part154.csC) (piBar (rhoBar 12519 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12519 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000195219329 : ℝ) ^ 2 + 0.000124219328 ^ 2 + 3 * 0.000072110238 ^ 2 +
        2 * 0.797885 * 0.000195219329 * 0.000124219328 + 2 * 0.000195219329 * 0.000072110238 +
        4 * 0.797885 * 0.000124219328 * 0.000072110238 := by gcongr
    _ ≤ (1.64581E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12519 BstLean.Part154.csC Θ ≤ 0.002668641264 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12519 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12519 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12519 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12519 BstLean.Part154.csC) (piBar (rhoBar 12519 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12519 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036069442350 * 1.64581E-7 / (0.000255586762 : ℝ) := by gcongr
    _ ≤ 0.002668641264 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12519 BstLean.Part154.csC Θ ≤ 0.002961750774 + 0.000674323195 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12519 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12519 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12519 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036069442350 : ℝ) * ((2 * Θ * 0.000255587158 +
        (6863 / 10000) * 0.000255587158 * 12519 * 0.001022413957) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002961750774 + 0.000674323195 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12519 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12519 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12519 0.011 Θ ∧ gammaRatio 12519 0.011 Θ ≤ 0.000087864256 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12519 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036069442350 : ℝ) * 0.525 / ((1 - 0.011) * 12519) := by gcongr
      _ ≤ (0.000087864256 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12519 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12519 0.011 Θ) :=
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
    badAllowance 12519 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000774418828 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12519 BstLean.Part154.csC) 1.22 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 2 (rhoBar 12519 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12519 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12519 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12519 0.011 Θ) 1.12 ≤ 3.3895E-8 := by
    have he : (17.2 : ℝ) ≤ gap 1 (gammaRatio 12519 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12519 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12519 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12519 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12519 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036069442350 : ℝ) * 12519 *
        (2.7751E-8 / 1.1045361 + 3.3895E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000774418828 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12519 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003736169602 + 0.003342964459 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12519

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12519
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12519 BstLean.Part154.csC) (piBar (rhoBar 12519 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12519 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12519 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12519 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12519 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12519 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12519 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12519 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12519 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12519 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12519 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12519 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12519 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12519 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12519 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052866489844 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12519) ≤ 0.010673476888 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12519 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036069442350)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010673476888 + 2 * 0.737676 / 12519) := by gcongr
    _ ≤ (0.052866489844 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12519 12 ≤ 0.0015 := by
  exact BstLean.Part269.S6.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12519

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12519
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560495264589 : ℝ) ≤ plow 12519 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12519) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052997825943)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001401036664) : eMP 12519 0.011 xi bn ≤ 0.001205915536 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12519 : ℝ) * (1 - 0.011))) ≤ 0.000596234010 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001401036664 / (12519 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000596234010 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000596234010 : ℝ) + 3.141593 * 0.052997825943 / (12519 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001205915536 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052997825943)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001401036664) : PiBarMP 12519 12 0.011 xi bn ≤ 0.162424535257 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12519 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037430424310 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.271249655964 : ℝ) ≤ √((12519 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.888337193829 : ℝ) ≤ √(12519 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12519) ≤ 0.124520648105 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037430424310 + 0.052997825943 * 1.772454 / (2 * (111.271249655964 : ℝ))) * (1 + 0.001205915536) +
        8 / (12519 * 111.888337193829) + 0.124520648105 := by gcongr
    _ ≤ (0.162424535257 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052997825943)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001401036664) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283079056710) :
    parallelOracle 12519 0.011 xi bn cd ≤ 0.163430012364 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12519 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12519 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560495264589 : ℝ) ≤ plow 12519 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.888337193829 : ℝ) ≤ √(12519 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.283079056710 : ℝ) / (2 * 0.560495264589 * 111.888337193829)) * 0.162424535257 +
        0.283079056710 ^ 2 / (2 * 0.560495264589 * 111.888337193829) := by gcongr
    _ ≤ (0.163430012364 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052997825943) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001401036664)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283079056710) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12519 12519 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560495264589 : ℝ) ≤ plow 12519 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.888337193829 : ℝ) ≤ √(12519 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12519 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12519 Θ 1.22 ≤ 0.011851999353 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.888337193829 := by gcongr <;> linarith
      _ ≤ (0.011851999353 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12519 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12519 12519 0.011 ≤ 0.008543223594 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12519 12519 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12519 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12519 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12519 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12519 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163430012364 + 0.011851999353 + (0.008543223594 : ℝ) *
        (1 + 2 * (0.283079056710 + 0.011851999353) / (0.560495264589 * 111.888337193829))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12519]

end BstLean.Part269.N12519

/-! The original eight local profiles supply actual 12519 moment certificates. -/
namespace BstLean.Part269.N12519
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12519 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12519 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12519 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052997825943 ∧
    0 ≤ bN 12519 BstLean.Part154.csC (groupTheta g) ∧ bN 12519 BstLean.Part154.csC (groupTheta g) ≤ 0.001401036664 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12519 12519 0.011
      (momentAllowance 12519 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12519 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12519 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12519 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12519 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12519 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230212566866 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12519 0.011
      (momentAllowance 12519 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12519 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12519
/-! The actual computed-centre upper energy formula at 12519. -/
namespace BstLean.Part269.N12519
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12519

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12519
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12519)
open BstLean.Part268 (cell12519)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086037012668
  | 2 => 0.086990249135
  | 3 => 0.087943225271
  | 4 => 0.088897722405
  | 5 => 0.089855882231
  | 6 => 0.090820258623
  | 7 => 0.091793874020
  | 8 => 0.092780280359
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12519 12519 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12519 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003740909217 + 0.003348232271 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S6.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12519

/-! Actual upper energy certificates on all 43 source endpoints at 12519. -/
namespace BstLean.Part269.N12519
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12519)
open BstLean.Part268 (cell12519)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12519 (gMinus 12519) (1 - (cell12519 i).lower) ≤ 1 ∧
    energyUpper 12519 (gMinus 12519) (BstLean.Part211.gPlus 12519)
      (finiteEnergy 12519 12519 0.011) (1 - (cell12519 i).lower) ≤
      (cell12519 i).energy := by
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
      have E := BstLean.Part269.S6.uniformEnergy10 (n := 12519) (by norm_num)
        (q := 1 - (cell12519 ⟨10,by decide⟩).lower)
        (by norm_num [cell12519]) (by norm_num [cell12519])
      exact ⟨E.1,E.2.trans (by norm_num [cell12519])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy11 (n := 12519) (by norm_num)
        (q := 1 - (cell12519 ⟨11,by decide⟩).lower)
        (by norm_num [cell12519]) (by norm_num [cell12519])
      exact ⟨E.1,E.2.trans (by norm_num [cell12519])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy12 (n := 12519) (by norm_num)
        (q := 1 - (cell12519 ⟨12,by decide⟩).lower)
        (by norm_num [cell12519]) (by norm_num [cell12519])
      exact ⟨E.1,E.2.trans (by norm_num [cell12519])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy13 (n := 12519) (by norm_num)
        (q := 1 - (cell12519 ⟨13,by decide⟩).lower)
        (by norm_num [cell12519]) (by norm_num [cell12519])
      exact ⟨E.1,E.2.trans (by norm_num [cell12519])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy14 (n := 12519) (by norm_num)
        (q := 1 - (cell12519 ⟨14,by decide⟩).lower)
        (by norm_num [cell12519]) (by norm_num [cell12519])
      exact ⟨E.1,E.2.trans (by norm_num [cell12519])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy15 (n := 12519) (by norm_num)
        (q := 1 - (cell12519 ⟨15,by decide⟩).lower)
        (by norm_num [cell12519]) (by norm_num [cell12519])
      exact ⟨E.1,E.2.trans (by norm_num [cell12519])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy16 (n := 12519) (by norm_num)
        (q := 1 - (cell12519 ⟨16,by decide⟩).lower)
        (by norm_num [cell12519]) (by norm_num [cell12519])
      exact ⟨E.1,E.2.trans (by norm_num [cell12519])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy17 (n := 12519) (by norm_num)
        (q := 1 - (cell12519 ⟨17,by decide⟩).lower)
        (by norm_num [cell12519]) (by norm_num [cell12519])
      exact ⟨E.1,E.2.trans (by norm_num [cell12519])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy18 (n := 12519) (by norm_num)
        (q := 1 - (cell12519 ⟨18,by decide⟩).lower)
        (by norm_num [cell12519]) (by norm_num [cell12519])
      exact ⟨E.1,E.2.trans (by norm_num [cell12519])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy19 (n := 12519) (by norm_num)
        (q := 1 - (cell12519 ⟨19,by decide⟩).lower)
        (by norm_num [cell12519]) (by norm_num [cell12519])
      exact ⟨E.1,E.2.trans (by norm_num [cell12519])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy20 (n := 12519) (by norm_num)
        (q := 1 - (cell12519 ⟨20,by decide⟩).lower)
        (by norm_num [cell12519]) (by norm_num [cell12519])
      exact ⟨E.1,E.2.trans (by norm_num [cell12519])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy21 (n := 12519) (by norm_num)
        (q := 1 - (cell12519 ⟨21,by decide⟩).lower)
        (by norm_num [cell12519]) (by norm_num [cell12519])
      exact ⟨E.1,E.2.trans (by norm_num [cell12519])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy22 (n := 12519) (by norm_num)
        (q := 1 - (cell12519 ⟨22,by decide⟩).lower)
        (by norm_num [cell12519]) (by norm_num [cell12519])
      exact ⟨E.1,E.2.trans (by norm_num [cell12519])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy23 (n := 12519) (by norm_num)
        (q := 1 - (cell12519 ⟨23,by decide⟩).lower)
        (by norm_num [cell12519]) (by norm_num [cell12519])
      exact ⟨E.1,E.2.trans (by norm_num [cell12519])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy24 (n := 12519) (by norm_num)
        (q := 1 - (cell12519 ⟨24,by decide⟩).lower)
        (by norm_num [cell12519]) (by norm_num [cell12519])
      exact ⟨E.1,E.2.trans (by norm_num [cell12519])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy25 (n := 12519) (by norm_num)
        (q := 1 - (cell12519 ⟨25,by decide⟩).lower)
        (by norm_num [cell12519]) (by norm_num [cell12519])
      exact ⟨E.1,E.2.trans (by norm_num [cell12519])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy26 (n := 12519) (by norm_num)
        (q := 1 - (cell12519 ⟨26,by decide⟩).lower)
        (by norm_num [cell12519]) (by norm_num [cell12519])
      exact ⟨E.1,E.2.trans (by norm_num [cell12519])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy27 (n := 12519) (by norm_num)
        (q := 1 - (cell12519 ⟨27,by decide⟩).lower)
        (by norm_num [cell12519]) (by norm_num [cell12519])
      exact ⟨E.1,E.2.trans (by norm_num [cell12519])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy28 (n := 12519) (by norm_num)
        (q := 1 - (cell12519 ⟨28,by decide⟩).lower)
        (by norm_num [cell12519]) (by norm_num [cell12519])
      exact ⟨E.1,E.2.trans (by norm_num [cell12519])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy29 (n := 12519) (by norm_num)
        (q := 1 - (cell12519 ⟨29,by decide⟩).lower)
        (by norm_num [cell12519]) (by norm_num [cell12519])
      exact ⟨E.1,E.2.trans (by norm_num [cell12519])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy30 (n := 12519) (by norm_num)
        (q := 1 - (cell12519 ⟨30,by decide⟩).lower)
        (by norm_num [cell12519]) (by norm_num [cell12519])
      exact ⟨E.1,E.2.trans (by norm_num [cell12519])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy31 (n := 12519) (by norm_num)
        (q := 1 - (cell12519 ⟨31,by decide⟩).lower)
        (by norm_num [cell12519]) (by norm_num [cell12519])
      exact ⟨E.1,E.2.trans (by norm_num [cell12519])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy32 (n := 12519) (by norm_num)
        (q := 1 - (cell12519 ⟨32,by decide⟩).lower)
        (by norm_num [cell12519]) (by norm_num [cell12519])
      exact ⟨E.1,E.2.trans (by norm_num [cell12519])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy33 (n := 12519) (by norm_num)
        (q := 1 - (cell12519 ⟨33,by decide⟩).lower)
        (by norm_num [cell12519]) (by norm_num [cell12519])
      exact ⟨E.1,E.2.trans (by norm_num [cell12519])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy34 (n := 12519) (by norm_num)
        (q := 1 - (cell12519 ⟨34,by decide⟩).lower)
        (by norm_num [cell12519]) (by norm_num [cell12519])
      exact ⟨E.1,E.2.trans (by norm_num [cell12519])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy35 (n := 12519) (by norm_num)
        (q := 1 - (cell12519 ⟨35,by decide⟩).lower)
        (by norm_num [cell12519]) (by norm_num [cell12519])
      exact ⟨E.1,E.2.trans (by norm_num [cell12519])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy36 (n := 12519) (by norm_num)
        (q := 1 - (cell12519 ⟨36,by decide⟩).lower)
        (by norm_num [cell12519]) (by norm_num [cell12519])
      exact ⟨E.1,E.2.trans (by norm_num [cell12519])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy37 (n := 12519) (by norm_num)
        (q := 1 - (cell12519 ⟨37,by decide⟩).lower)
        (by norm_num [cell12519]) (by norm_num [cell12519])
      exact ⟨E.1,E.2.trans (by norm_num [cell12519])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy38 (n := 12519) (by norm_num)
        (q := 1 - (cell12519 ⟨38,by decide⟩).lower)
        (by norm_num [cell12519]) (by norm_num [cell12519])
      exact ⟨E.1,E.2.trans (by norm_num [cell12519])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy39 (n := 12519) (by norm_num)
        (q := 1 - (cell12519 ⟨39,by decide⟩).lower)
        (by norm_num [cell12519]) (by norm_num [cell12519])
      exact ⟨E.1,E.2.trans (by norm_num [cell12519])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy40 (n := 12519) (by norm_num)
        (q := 1 - (cell12519 ⟨40,by decide⟩).lower)
        (by norm_num [cell12519]) (by norm_num [cell12519])
      exact ⟨E.1,E.2.trans (by norm_num [cell12519])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy41 (n := 12519) (by norm_num)
        (q := 1 - (cell12519 ⟨41,by decide⟩).lower)
        (by norm_num [cell12519]) (by norm_num [cell12519])
      exact ⟨E.1,E.2.trans (by norm_num [cell12519])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy42 (n := 12519) (by norm_num)
        (q := 1 - (cell12519 ⟨42,by decide⟩).lower)
        (by norm_num [cell12519]) (by norm_num [cell12519])
      exact ⟨E.1,E.2.trans (by norm_num [cell12519])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy43 (n := 12519) (by norm_num)
        (q := 1 - (cell12519 ⟨43,by decide⟩).lower)
        (by norm_num [cell12519]) (by norm_num [cell12519])
      exact ⟨E.1,E.2.trans (by norm_num [cell12519])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy44 (n := 12519) (by norm_num)
        (q := 1 - (cell12519 ⟨44,by decide⟩).lower)
        (by norm_num [cell12519]) (by norm_num [cell12519])
      exact ⟨E.1,E.2.trans (by norm_num [cell12519])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy45 (n := 12519) (by norm_num)
        (q := 1 - (cell12519 ⟨45,by decide⟩).lower)
        (by norm_num [cell12519]) (by norm_num [cell12519])
      exact ⟨E.1,E.2.trans (by norm_num [cell12519])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy46 (n := 12519) (by norm_num)
        (q := 1 - (cell12519 ⟨46,by decide⟩).lower)
        (by norm_num [cell12519]) (by norm_num [cell12519])
      exact ⟨E.1,E.2.trans (by norm_num [cell12519])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy47 (n := 12519) (by norm_num)
        (q := 1 - (cell12519 ⟨47,by decide⟩).lower)
        (by norm_num [cell12519]) (by norm_num [cell12519])
      exact ⟨E.1,E.2.trans (by norm_num [cell12519])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy48 (n := 12519) (by norm_num)
        (q := 1 - (cell12519 ⟨48,by decide⟩).lower)
        (by norm_num [cell12519]) (by norm_num [cell12519])
      exact ⟨E.1,E.2.trans (by norm_num [cell12519])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy49 (n := 12519) (by norm_num)
        (q := 1 - (cell12519 ⟨49,by decide⟩).lower)
        (by norm_num [cell12519]) (by norm_num [cell12519])
      exact ⟨E.1,E.2.trans (by norm_num [cell12519])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy50 (n := 12519) (by norm_num)
        (q := 1 - (cell12519 ⟨50,by decide⟩).lower)
        (by norm_num [cell12519]) (by norm_num [cell12519])
      exact ⟨E.1,E.2.trans (by norm_num [cell12519])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy51 (n := 12519) (by norm_num)
        (q := 1 - (cell12519 ⟨51,by decide⟩).lower)
        (by norm_num [cell12519]) (by norm_num [cell12519])
      exact ⟨E.1,E.2.trans (by norm_num [cell12519])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy52 (n := 12519) (by norm_num)
        (q := 1 - (cell12519 ⟨52,by decide⟩).lower)
        (by norm_num [cell12519]) (by norm_num [cell12519])
      exact ⟨E.1,E.2.trans (by norm_num [cell12519])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12519

/-! Source-cell containment and simple scalar guards at 12519. -/
namespace BstLean.Part269.N12519
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12519)
open BstLean.Part268 (cell12519)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12519 ⟨10,by decide⟩).lower ∧ (cell12519 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12519 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12519 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12519 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12519 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12519 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12519,cell12519,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12519 ⟨11,by decide⟩).lower ∧ (cell12519 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12519 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12519 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12519 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12519 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12519 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12519,cell12519,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12519 ⟨12,by decide⟩).lower ∧ (cell12519 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12519 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12519 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12519 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12519 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12519 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12519,cell12519,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12519 ⟨13,by decide⟩).lower ∧ (cell12519 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12519 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12519 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12519 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12519 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12519 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12519,cell12519,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12519 ⟨14,by decide⟩).lower ∧ (cell12519 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12519 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12519 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12519 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12519 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12519 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12519,cell12519,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12519 ⟨15,by decide⟩).lower ∧ (cell12519 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12519 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12519 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12519 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12519 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12519 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12519,cell12519,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12519 ⟨16,by decide⟩).lower ∧ (cell12519 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12519 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12519 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12519 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12519 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12519 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12519,cell12519,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12519 ⟨17,by decide⟩).lower ∧ (cell12519 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12519 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12519 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12519 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12519 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12519 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12519,cell12519,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12519 ⟨18,by decide⟩).lower ∧ (cell12519 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12519 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12519 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12519 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12519 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12519 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12519,cell12519,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12519 ⟨19,by decide⟩).lower ∧ (cell12519 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12519 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12519 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12519 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12519 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12519 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12519,cell12519,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12519 ⟨20,by decide⟩).lower ∧ (cell12519 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12519 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12519 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12519 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12519 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12519 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12519,cell12519,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12519 ⟨21,by decide⟩).lower ∧ (cell12519 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12519 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12519 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12519 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12519 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12519 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12519,cell12519,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12519 ⟨22,by decide⟩).lower ∧ (cell12519 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12519 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12519 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12519 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12519 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12519 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12519,cell12519,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12519 ⟨23,by decide⟩).lower ∧ (cell12519 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12519 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12519 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12519 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12519 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12519 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12519,cell12519,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12519 ⟨24,by decide⟩).lower ∧ (cell12519 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12519 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12519 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12519 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12519 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12519 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12519,cell12519,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12519 ⟨25,by decide⟩).lower ∧ (cell12519 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12519 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12519 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12519 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12519 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12519 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12519,cell12519,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12519 ⟨26,by decide⟩).lower ∧ (cell12519 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12519 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12519 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12519 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12519 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12519 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12519,cell12519,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12519 ⟨27,by decide⟩).lower ∧ (cell12519 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12519 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12519 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12519 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12519 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12519 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12519,cell12519,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12519 ⟨28,by decide⟩).lower ∧ (cell12519 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12519 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12519 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12519 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12519 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12519 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12519,cell12519,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12519 ⟨29,by decide⟩).lower ∧ (cell12519 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12519 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12519 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12519 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12519 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12519 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12519,cell12519,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12519 ⟨30,by decide⟩).lower ∧ (cell12519 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12519 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12519 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12519 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12519 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12519 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12519,cell12519,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12519 ⟨31,by decide⟩).lower ∧ (cell12519 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12519 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12519 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12519 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12519 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12519 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12519,cell12519,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12519 ⟨32,by decide⟩).lower ∧ (cell12519 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12519 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12519 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12519 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12519 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12519 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12519,cell12519,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12519 ⟨33,by decide⟩).lower ∧ (cell12519 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12519 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12519 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12519 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12519 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12519 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12519,cell12519,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12519 ⟨34,by decide⟩).lower ∧ (cell12519 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12519 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12519 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12519 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12519 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12519 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12519,cell12519,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12519 ⟨35,by decide⟩).lower ∧ (cell12519 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12519 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12519 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12519 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12519 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12519 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12519,cell12519,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12519 ⟨36,by decide⟩).lower ∧ (cell12519 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12519 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12519 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12519 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12519 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12519 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12519,cell12519,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12519 ⟨37,by decide⟩).lower ∧ (cell12519 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12519 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12519 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12519 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12519 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12519 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12519,cell12519,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12519 ⟨38,by decide⟩).lower ∧ (cell12519 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12519 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12519 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12519 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12519 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12519 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12519,cell12519,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12519 ⟨39,by decide⟩).lower ∧ (cell12519 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12519 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12519 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12519 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12519 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12519 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12519,cell12519,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12519 ⟨40,by decide⟩).lower ∧ (cell12519 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12519 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12519 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12519 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12519 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12519 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12519,cell12519,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12519 ⟨41,by decide⟩).lower ∧ (cell12519 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12519 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12519 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12519 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12519 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12519 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12519,cell12519,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12519 ⟨42,by decide⟩).lower ∧ (cell12519 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12519 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12519 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12519 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12519 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12519 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12519,cell12519,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12519 ⟨43,by decide⟩).lower ∧ (cell12519 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12519 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12519 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12519 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12519 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12519 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12519,cell12519,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12519 ⟨44,by decide⟩).lower ∧ (cell12519 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12519 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12519 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12519 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12519 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12519 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12519,cell12519,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12519 ⟨45,by decide⟩).lower ∧ (cell12519 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12519 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12519 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12519 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12519 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12519 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12519,cell12519,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12519 ⟨46,by decide⟩).lower ∧ (cell12519 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12519 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12519 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12519 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12519 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12519 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12519,cell12519,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12519 ⟨47,by decide⟩).lower ∧ (cell12519 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12519 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12519 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12519 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12519 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12519 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12519,cell12519,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12519 ⟨48,by decide⟩).lower ∧ (cell12519 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12519 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12519 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12519 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12519 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12519 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12519,cell12519,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12519 ⟨49,by decide⟩).lower ∧ (cell12519 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12519 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12519 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12519 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12519 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12519 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12519,cell12519,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12519 ⟨50,by decide⟩).lower ∧ (cell12519 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12519 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12519 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12519 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12519 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12519 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12519,cell12519,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12519 ⟨51,by decide⟩).lower ∧ (cell12519 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12519 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12519 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12519 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12519 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12519 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12519,cell12519,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12519 ⟨52,by decide⟩).lower ∧ (cell12519 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12519 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12519 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12519 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12519 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12519 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12519,cell12519,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12519 i).lower ∧
    (cell12519 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12519 i).upper ≤ (0.532 : ℝ) ∧
    (cell12519 i).centre ≤ (0.1 : ℝ) ∧ (cell12519 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12519 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12519 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12519

/-! The local source numeric instances at 12519 have no network premises. -/
namespace BstLean.Part269.N12519
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12519)
open BstLean.Part268 (cell12519)

noncomputable def sourceNumerics12519 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12519 (cell12519 i)
      scalarRow12519.M scalarRow12519.H scalarRow12519.xi := by
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
    energy_allowance := scalarRow12519.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12519]
    centre_nonneg := (scalarRow12519.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D6.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12519])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12519
/-! Actual 12520 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12520
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12520 ≤ (1.036067989089 : ℝ) := by
  have hr : (111.892805845594 : ℝ) ≤ √(12520 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.892805845594 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12520 12520 (11 / 1000) ≤
    (0.008542882402 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12520) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.892805845594 : ℝ) ≤ √(12520 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12520)
  have hdiv : K / √(12520 : ℝ) ≤ K / 111.892805845594 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.892805845594 ≤ (0.008542882402 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12520.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12520 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12520 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12520 := gPlus_lower 12520
end BstLean.Part269.N12520

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12520
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036067989088 : ℝ) ≤ wn 12520 := by
  have hn : √(12520 : ℝ) ≤ 111.892805845595 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12520 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.892805845595 ≤ 2 / √(12520 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000255565990 : ℝ) ≤ rhoBar 12520 BstLean.Part154.csC ∧
    rhoBar 12520 BstLean.Part154.csC ≤ 0.000255566385 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036067989088 : ℝ) / (1.295212 * 12520) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036067989089 : ℝ) / (1.29521 * 12520) := by gcongr
      _ ≤ (0.000255566385 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12520 BstLean.Part154.csC) ≤ 0.001022330855 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12520 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12520 BstLean.Part154.csC) (piBar (rhoBar 12520 BstLean.Part154.csC)) ≤ 0.000195203462 ∧
    cc1 (rhoBar 12520 BstLean.Part154.csC) (piBar (rhoBar 12520 BstLean.Part154.csC)) ≤ 0.000124209232 ∧
    cc2 (rhoBar 12520 BstLean.Part154.csC) ≤ 0.000072104377 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12520 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12520 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12520 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12520 BstLean.Part154.csC * nuR (rhoBar 12520 BstLean.Part154.csC)) ≤ 0.000511149099 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000255566385 : ℝ) * 0.001022330855 := by gcongr
      _ ≤ (0.000511149099 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12520 BstLean.Part154.csC) * nuR (rhoBar 12520 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001022330855 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12520 BstLean.Part154.csC) * rhoBar 12520 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000255566385 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000255566385 / 2 + 0.399 * 0.001022330855 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000195203462 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000511149099 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124209232 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000255566385 / 1.414213562 := by gcongr
      _ ≤ (0.000072104377 : ℝ) := by norm_num

end BstLean.Part269.N12520

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12520
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12520 BstLean.Part154.csC) (piBar (rhoBar 12520 BstLean.Part154.csC)) ≤ 1.64555E-7 := by
  have hr0 : 0 ≤ rhoBar 12520 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12520 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12520 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12520 BstLean.Part154.csC) (piBar (rhoBar 12520 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12520 BstLean.Part154.csC) (piBar (rhoBar 12520 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12520 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000195203462 : ℝ) ^ 2 + 0.000124209232 ^ 2 + 3 * 0.000072104377 ^ 2 +
        2 * 0.797885 * 0.000195203462 * 0.000124209232 + 2 * 0.000195203462 * 0.000072104377 +
        4 * 0.797885 * 0.000124209232 * 0.000072104377 := by gcongr
    _ ≤ (1.64555E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12520 BstLean.Part154.csC Θ ≤ 0.002668432806 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12520 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12520 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12520 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12520 BstLean.Part154.csC) (piBar (rhoBar 12520 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12520 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036067989089 * 1.64555E-7 / (0.000255565990 : ℝ) := by gcongr
    _ ≤ 0.002668432806 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12520 BstLean.Part154.csC Θ ≤ 0.002961501731 + 0.000674267443 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12520 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12520 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12520 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036067989089 : ℝ) * ((2 * Θ * 0.000255566385 +
        (6863 / 10000) * 0.000255566385 * 12520 * 0.001022330855) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002961501731 + 0.000674267443 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12520 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12520 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12520 0.011 Θ ∧ gammaRatio 12520 0.011 Θ ≤ 0.000087857115 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12520 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036067989089 : ℝ) * 0.525 / ((1 - 0.011) * 12520) := by gcongr
      _ ≤ (0.000087857115 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12520 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12520 0.011 Θ) :=
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
    badAllowance 12520 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000774418828 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12520 BstLean.Part154.csC) 1.22 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 2 (rhoBar 12520 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12520 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12520 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12520 0.011 Θ) 1.12 ≤ 3.3895E-8 := by
    have he : (17.2 : ℝ) ≤ gap 1 (gammaRatio 12520 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12520 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12520 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12520 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12520 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036067989089 : ℝ) * 12520 *
        (2.7751E-8 / 1.1045361 + 3.3895E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000774418828 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12520 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003735920559 + 0.003342700249 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12520

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12520
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12520 BstLean.Part154.csC) (piBar (rhoBar 12520 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12520 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12520 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12520 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12520 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12520 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12520 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12520 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12520 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12520 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12520 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12520 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12520 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12520 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12520 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052864355467 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12520) ≤ 0.010673050623 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12520 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036067989089)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010673050623 + 2 * 0.737676 / 12520) := by gcongr
    _ ≤ (0.052864355467 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12520 12 ≤ 0.0015 := by
  exact BstLean.Part269.S6.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12520

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12520
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560495311126 : ℝ) ≤ plow 12520 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12520) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052997438190)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001400927224) : eMP 12520 0.011 xi bn ≤ 0.001205820167 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12520 : ℝ) * (1 - 0.011))) ≤ 0.000596186912 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001400927224 / (12520 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000596186912 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000596186912 : ℝ) + 3.141593 * 0.052997438190 / (12520 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001205820167 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052997438190)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001400927224) : PiBarMP 12520 12 0.011 xi bn ≤ 0.162418074321 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12520 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037428962369 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.275693662183 : ℝ) ≤ √((12520 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.892805845594 : ℝ) ≤ √(12520 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12520) ≤ 0.124515675137 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037428962369 + 0.052997438190 * 1.772454 / (2 * (111.275693662183 : ℝ))) * (1 + 0.001205820167) +
        8 / (12520 * 111.892805845594) + 0.124515675137 := by gcongr
    _ ≤ (0.162418074321 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052997438190)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001400927224) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283076080169) :
    parallelOracle 12520 0.011 xi bn cd ≤ 0.163423479318 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12520 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12520 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560495311126 : ℝ) ≤ plow 12520 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.892805845594 : ℝ) ≤ √(12520 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.283076080169 : ℝ) / (2 * 0.560495311126 * 111.892805845594)) * 0.162418074321 +
        0.283076080169 ^ 2 / (2 * 0.560495311126 * 111.892805845594) := by gcongr
    _ ≤ (0.163423479318 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052997438190) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001400927224)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283076080169) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12520 12520 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560495311126 : ℝ) ≤ plow 12520 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.892805845594 : ℝ) ≤ √(12520 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12520 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12520 Θ 1.22 ≤ 0.011851526021 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.892805845594 := by gcongr <;> linarith
      _ ≤ (0.011851526021 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12520 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12520 12520 0.011 ≤ 0.008542882402 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12520 12520 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12520 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12520 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12520 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12520 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163423479318 + 0.011851526021 + (0.008542882402 : ℝ) *
        (1 + 2 * (0.283076080169 + 0.011851526021) / (0.560495311126 * 111.892805845594))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12520]

end BstLean.Part269.N12520

/-! The original eight local profiles supply actual 12520 moment certificates. -/
namespace BstLean.Part269.N12520
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12520 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12520 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12520 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052997438190 ∧
    0 ≤ bN 12520 BstLean.Part154.csC (groupTheta g) ∧ bN 12520 BstLean.Part154.csC (groupTheta g) ≤ 0.001400927224 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12520 12520 0.011
      (momentAllowance 12520 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12520 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12520 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12520 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12520 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12520 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230211724702 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12520 0.011
      (momentAllowance 12520 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12520 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12520
/-! The actual computed-centre upper energy formula at 12520. -/
namespace BstLean.Part269.N12520
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12520

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12520
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12520)
open BstLean.Part268 (cell12520)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086033881360
  | 2 => 0.086987055196
  | 3 => 0.087939958762
  | 4 => 0.088894371160
  | 5 => 0.089852431475
  | 6 => 0.090816690544
  | 7 => 0.091790167294
  | 8 => 0.092776409627
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12520 12520 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12520 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003740909217 + 0.003348232271 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S6.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12520

/-! Actual upper energy certificates on all 43 source endpoints at 12520. -/
namespace BstLean.Part269.N12520
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12520)
open BstLean.Part268 (cell12520)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12520 (gMinus 12520) (1 - (cell12520 i).lower) ≤ 1 ∧
    energyUpper 12520 (gMinus 12520) (BstLean.Part211.gPlus 12520)
      (finiteEnergy 12520 12520 0.011) (1 - (cell12520 i).lower) ≤
      (cell12520 i).energy := by
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
      have E := BstLean.Part269.S6.uniformEnergy10 (n := 12520) (by norm_num)
        (q := 1 - (cell12520 ⟨10,by decide⟩).lower)
        (by norm_num [cell12520]) (by norm_num [cell12520])
      exact ⟨E.1,E.2.trans (by norm_num [cell12520])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy11 (n := 12520) (by norm_num)
        (q := 1 - (cell12520 ⟨11,by decide⟩).lower)
        (by norm_num [cell12520]) (by norm_num [cell12520])
      exact ⟨E.1,E.2.trans (by norm_num [cell12520])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy12 (n := 12520) (by norm_num)
        (q := 1 - (cell12520 ⟨12,by decide⟩).lower)
        (by norm_num [cell12520]) (by norm_num [cell12520])
      exact ⟨E.1,E.2.trans (by norm_num [cell12520])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy13 (n := 12520) (by norm_num)
        (q := 1 - (cell12520 ⟨13,by decide⟩).lower)
        (by norm_num [cell12520]) (by norm_num [cell12520])
      exact ⟨E.1,E.2.trans (by norm_num [cell12520])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy14 (n := 12520) (by norm_num)
        (q := 1 - (cell12520 ⟨14,by decide⟩).lower)
        (by norm_num [cell12520]) (by norm_num [cell12520])
      exact ⟨E.1,E.2.trans (by norm_num [cell12520])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy15 (n := 12520) (by norm_num)
        (q := 1 - (cell12520 ⟨15,by decide⟩).lower)
        (by norm_num [cell12520]) (by norm_num [cell12520])
      exact ⟨E.1,E.2.trans (by norm_num [cell12520])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy16 (n := 12520) (by norm_num)
        (q := 1 - (cell12520 ⟨16,by decide⟩).lower)
        (by norm_num [cell12520]) (by norm_num [cell12520])
      exact ⟨E.1,E.2.trans (by norm_num [cell12520])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy17 (n := 12520) (by norm_num)
        (q := 1 - (cell12520 ⟨17,by decide⟩).lower)
        (by norm_num [cell12520]) (by norm_num [cell12520])
      exact ⟨E.1,E.2.trans (by norm_num [cell12520])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy18 (n := 12520) (by norm_num)
        (q := 1 - (cell12520 ⟨18,by decide⟩).lower)
        (by norm_num [cell12520]) (by norm_num [cell12520])
      exact ⟨E.1,E.2.trans (by norm_num [cell12520])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy19 (n := 12520) (by norm_num)
        (q := 1 - (cell12520 ⟨19,by decide⟩).lower)
        (by norm_num [cell12520]) (by norm_num [cell12520])
      exact ⟨E.1,E.2.trans (by norm_num [cell12520])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy20 (n := 12520) (by norm_num)
        (q := 1 - (cell12520 ⟨20,by decide⟩).lower)
        (by norm_num [cell12520]) (by norm_num [cell12520])
      exact ⟨E.1,E.2.trans (by norm_num [cell12520])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy21 (n := 12520) (by norm_num)
        (q := 1 - (cell12520 ⟨21,by decide⟩).lower)
        (by norm_num [cell12520]) (by norm_num [cell12520])
      exact ⟨E.1,E.2.trans (by norm_num [cell12520])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy22 (n := 12520) (by norm_num)
        (q := 1 - (cell12520 ⟨22,by decide⟩).lower)
        (by norm_num [cell12520]) (by norm_num [cell12520])
      exact ⟨E.1,E.2.trans (by norm_num [cell12520])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy23 (n := 12520) (by norm_num)
        (q := 1 - (cell12520 ⟨23,by decide⟩).lower)
        (by norm_num [cell12520]) (by norm_num [cell12520])
      exact ⟨E.1,E.2.trans (by norm_num [cell12520])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy24 (n := 12520) (by norm_num)
        (q := 1 - (cell12520 ⟨24,by decide⟩).lower)
        (by norm_num [cell12520]) (by norm_num [cell12520])
      exact ⟨E.1,E.2.trans (by norm_num [cell12520])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy25 (n := 12520) (by norm_num)
        (q := 1 - (cell12520 ⟨25,by decide⟩).lower)
        (by norm_num [cell12520]) (by norm_num [cell12520])
      exact ⟨E.1,E.2.trans (by norm_num [cell12520])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy26 (n := 12520) (by norm_num)
        (q := 1 - (cell12520 ⟨26,by decide⟩).lower)
        (by norm_num [cell12520]) (by norm_num [cell12520])
      exact ⟨E.1,E.2.trans (by norm_num [cell12520])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy27 (n := 12520) (by norm_num)
        (q := 1 - (cell12520 ⟨27,by decide⟩).lower)
        (by norm_num [cell12520]) (by norm_num [cell12520])
      exact ⟨E.1,E.2.trans (by norm_num [cell12520])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy28 (n := 12520) (by norm_num)
        (q := 1 - (cell12520 ⟨28,by decide⟩).lower)
        (by norm_num [cell12520]) (by norm_num [cell12520])
      exact ⟨E.1,E.2.trans (by norm_num [cell12520])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy29 (n := 12520) (by norm_num)
        (q := 1 - (cell12520 ⟨29,by decide⟩).lower)
        (by norm_num [cell12520]) (by norm_num [cell12520])
      exact ⟨E.1,E.2.trans (by norm_num [cell12520])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy30 (n := 12520) (by norm_num)
        (q := 1 - (cell12520 ⟨30,by decide⟩).lower)
        (by norm_num [cell12520]) (by norm_num [cell12520])
      exact ⟨E.1,E.2.trans (by norm_num [cell12520])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy31 (n := 12520) (by norm_num)
        (q := 1 - (cell12520 ⟨31,by decide⟩).lower)
        (by norm_num [cell12520]) (by norm_num [cell12520])
      exact ⟨E.1,E.2.trans (by norm_num [cell12520])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy32 (n := 12520) (by norm_num)
        (q := 1 - (cell12520 ⟨32,by decide⟩).lower)
        (by norm_num [cell12520]) (by norm_num [cell12520])
      exact ⟨E.1,E.2.trans (by norm_num [cell12520])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy33 (n := 12520) (by norm_num)
        (q := 1 - (cell12520 ⟨33,by decide⟩).lower)
        (by norm_num [cell12520]) (by norm_num [cell12520])
      exact ⟨E.1,E.2.trans (by norm_num [cell12520])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy34 (n := 12520) (by norm_num)
        (q := 1 - (cell12520 ⟨34,by decide⟩).lower)
        (by norm_num [cell12520]) (by norm_num [cell12520])
      exact ⟨E.1,E.2.trans (by norm_num [cell12520])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy35 (n := 12520) (by norm_num)
        (q := 1 - (cell12520 ⟨35,by decide⟩).lower)
        (by norm_num [cell12520]) (by norm_num [cell12520])
      exact ⟨E.1,E.2.trans (by norm_num [cell12520])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy36 (n := 12520) (by norm_num)
        (q := 1 - (cell12520 ⟨36,by decide⟩).lower)
        (by norm_num [cell12520]) (by norm_num [cell12520])
      exact ⟨E.1,E.2.trans (by norm_num [cell12520])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy37 (n := 12520) (by norm_num)
        (q := 1 - (cell12520 ⟨37,by decide⟩).lower)
        (by norm_num [cell12520]) (by norm_num [cell12520])
      exact ⟨E.1,E.2.trans (by norm_num [cell12520])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy38 (n := 12520) (by norm_num)
        (q := 1 - (cell12520 ⟨38,by decide⟩).lower)
        (by norm_num [cell12520]) (by norm_num [cell12520])
      exact ⟨E.1,E.2.trans (by norm_num [cell12520])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy39 (n := 12520) (by norm_num)
        (q := 1 - (cell12520 ⟨39,by decide⟩).lower)
        (by norm_num [cell12520]) (by norm_num [cell12520])
      exact ⟨E.1,E.2.trans (by norm_num [cell12520])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy40 (n := 12520) (by norm_num)
        (q := 1 - (cell12520 ⟨40,by decide⟩).lower)
        (by norm_num [cell12520]) (by norm_num [cell12520])
      exact ⟨E.1,E.2.trans (by norm_num [cell12520])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy41 (n := 12520) (by norm_num)
        (q := 1 - (cell12520 ⟨41,by decide⟩).lower)
        (by norm_num [cell12520]) (by norm_num [cell12520])
      exact ⟨E.1,E.2.trans (by norm_num [cell12520])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy42 (n := 12520) (by norm_num)
        (q := 1 - (cell12520 ⟨42,by decide⟩).lower)
        (by norm_num [cell12520]) (by norm_num [cell12520])
      exact ⟨E.1,E.2.trans (by norm_num [cell12520])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy43 (n := 12520) (by norm_num)
        (q := 1 - (cell12520 ⟨43,by decide⟩).lower)
        (by norm_num [cell12520]) (by norm_num [cell12520])
      exact ⟨E.1,E.2.trans (by norm_num [cell12520])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy44 (n := 12520) (by norm_num)
        (q := 1 - (cell12520 ⟨44,by decide⟩).lower)
        (by norm_num [cell12520]) (by norm_num [cell12520])
      exact ⟨E.1,E.2.trans (by norm_num [cell12520])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy45 (n := 12520) (by norm_num)
        (q := 1 - (cell12520 ⟨45,by decide⟩).lower)
        (by norm_num [cell12520]) (by norm_num [cell12520])
      exact ⟨E.1,E.2.trans (by norm_num [cell12520])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy46 (n := 12520) (by norm_num)
        (q := 1 - (cell12520 ⟨46,by decide⟩).lower)
        (by norm_num [cell12520]) (by norm_num [cell12520])
      exact ⟨E.1,E.2.trans (by norm_num [cell12520])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy47 (n := 12520) (by norm_num)
        (q := 1 - (cell12520 ⟨47,by decide⟩).lower)
        (by norm_num [cell12520]) (by norm_num [cell12520])
      exact ⟨E.1,E.2.trans (by norm_num [cell12520])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy48 (n := 12520) (by norm_num)
        (q := 1 - (cell12520 ⟨48,by decide⟩).lower)
        (by norm_num [cell12520]) (by norm_num [cell12520])
      exact ⟨E.1,E.2.trans (by norm_num [cell12520])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy49 (n := 12520) (by norm_num)
        (q := 1 - (cell12520 ⟨49,by decide⟩).lower)
        (by norm_num [cell12520]) (by norm_num [cell12520])
      exact ⟨E.1,E.2.trans (by norm_num [cell12520])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy50 (n := 12520) (by norm_num)
        (q := 1 - (cell12520 ⟨50,by decide⟩).lower)
        (by norm_num [cell12520]) (by norm_num [cell12520])
      exact ⟨E.1,E.2.trans (by norm_num [cell12520])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy51 (n := 12520) (by norm_num)
        (q := 1 - (cell12520 ⟨51,by decide⟩).lower)
        (by norm_num [cell12520]) (by norm_num [cell12520])
      exact ⟨E.1,E.2.trans (by norm_num [cell12520])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy52 (n := 12520) (by norm_num)
        (q := 1 - (cell12520 ⟨52,by decide⟩).lower)
        (by norm_num [cell12520]) (by norm_num [cell12520])
      exact ⟨E.1,E.2.trans (by norm_num [cell12520])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12520

/-! Source-cell containment and simple scalar guards at 12520. -/
namespace BstLean.Part269.N12520
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12520)
open BstLean.Part268 (cell12520)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12520 ⟨10,by decide⟩).lower ∧ (cell12520 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12520 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12520 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12520 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12520 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12520 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12520,cell12520,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12520 ⟨11,by decide⟩).lower ∧ (cell12520 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12520 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12520 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12520 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12520 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12520 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12520,cell12520,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12520 ⟨12,by decide⟩).lower ∧ (cell12520 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12520 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12520 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12520 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12520 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12520 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12520,cell12520,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12520 ⟨13,by decide⟩).lower ∧ (cell12520 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12520 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12520 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12520 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12520 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12520 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12520,cell12520,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12520 ⟨14,by decide⟩).lower ∧ (cell12520 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12520 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12520 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12520 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12520 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12520 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12520,cell12520,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12520 ⟨15,by decide⟩).lower ∧ (cell12520 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12520 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12520 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12520 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12520 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12520 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12520,cell12520,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12520 ⟨16,by decide⟩).lower ∧ (cell12520 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12520 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12520 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12520 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12520 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12520 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12520,cell12520,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12520 ⟨17,by decide⟩).lower ∧ (cell12520 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12520 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12520 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12520 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12520 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12520 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12520,cell12520,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12520 ⟨18,by decide⟩).lower ∧ (cell12520 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12520 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12520 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12520 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12520 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12520 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12520,cell12520,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12520 ⟨19,by decide⟩).lower ∧ (cell12520 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12520 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12520 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12520 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12520 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12520 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12520,cell12520,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12520 ⟨20,by decide⟩).lower ∧ (cell12520 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12520 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12520 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12520 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12520 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12520 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12520,cell12520,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12520 ⟨21,by decide⟩).lower ∧ (cell12520 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12520 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12520 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12520 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12520 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12520 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12520,cell12520,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12520 ⟨22,by decide⟩).lower ∧ (cell12520 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12520 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12520 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12520 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12520 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12520 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12520,cell12520,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12520 ⟨23,by decide⟩).lower ∧ (cell12520 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12520 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12520 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12520 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12520 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12520 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12520,cell12520,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12520 ⟨24,by decide⟩).lower ∧ (cell12520 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12520 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12520 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12520 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12520 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12520 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12520,cell12520,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12520 ⟨25,by decide⟩).lower ∧ (cell12520 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12520 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12520 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12520 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12520 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12520 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12520,cell12520,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12520 ⟨26,by decide⟩).lower ∧ (cell12520 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12520 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12520 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12520 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12520 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12520 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12520,cell12520,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12520 ⟨27,by decide⟩).lower ∧ (cell12520 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12520 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12520 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12520 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12520 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12520 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12520,cell12520,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12520 ⟨28,by decide⟩).lower ∧ (cell12520 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12520 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12520 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12520 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12520 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12520 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12520,cell12520,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12520 ⟨29,by decide⟩).lower ∧ (cell12520 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12520 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12520 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12520 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12520 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12520 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12520,cell12520,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12520 ⟨30,by decide⟩).lower ∧ (cell12520 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12520 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12520 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12520 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12520 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12520 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12520,cell12520,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12520 ⟨31,by decide⟩).lower ∧ (cell12520 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12520 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12520 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12520 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12520 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12520 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12520,cell12520,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12520 ⟨32,by decide⟩).lower ∧ (cell12520 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12520 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12520 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12520 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12520 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12520 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12520,cell12520,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12520 ⟨33,by decide⟩).lower ∧ (cell12520 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12520 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12520 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12520 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12520 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12520 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12520,cell12520,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12520 ⟨34,by decide⟩).lower ∧ (cell12520 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12520 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12520 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12520 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12520 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12520 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12520,cell12520,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12520 ⟨35,by decide⟩).lower ∧ (cell12520 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12520 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12520 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12520 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12520 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12520 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12520,cell12520,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12520 ⟨36,by decide⟩).lower ∧ (cell12520 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12520 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12520 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12520 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12520 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12520 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12520,cell12520,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12520 ⟨37,by decide⟩).lower ∧ (cell12520 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12520 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12520 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12520 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12520 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12520 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12520,cell12520,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12520 ⟨38,by decide⟩).lower ∧ (cell12520 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12520 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12520 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12520 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12520 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12520 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12520,cell12520,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12520 ⟨39,by decide⟩).lower ∧ (cell12520 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12520 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12520 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12520 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12520 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12520 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12520,cell12520,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12520 ⟨40,by decide⟩).lower ∧ (cell12520 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12520 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12520 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12520 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12520 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12520 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12520,cell12520,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12520 ⟨41,by decide⟩).lower ∧ (cell12520 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12520 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12520 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12520 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12520 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12520 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12520,cell12520,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12520 ⟨42,by decide⟩).lower ∧ (cell12520 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12520 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12520 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12520 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12520 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12520 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12520,cell12520,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12520 ⟨43,by decide⟩).lower ∧ (cell12520 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12520 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12520 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12520 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12520 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12520 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12520,cell12520,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12520 ⟨44,by decide⟩).lower ∧ (cell12520 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12520 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12520 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12520 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12520 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12520 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12520,cell12520,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12520 ⟨45,by decide⟩).lower ∧ (cell12520 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12520 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12520 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12520 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12520 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12520 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12520,cell12520,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12520 ⟨46,by decide⟩).lower ∧ (cell12520 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12520 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12520 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12520 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12520 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12520 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12520,cell12520,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12520 ⟨47,by decide⟩).lower ∧ (cell12520 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12520 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12520 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12520 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12520 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12520 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12520,cell12520,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12520 ⟨48,by decide⟩).lower ∧ (cell12520 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12520 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12520 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12520 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12520 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12520 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12520,cell12520,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12520 ⟨49,by decide⟩).lower ∧ (cell12520 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12520 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12520 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12520 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12520 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12520 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12520,cell12520,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12520 ⟨50,by decide⟩).lower ∧ (cell12520 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12520 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12520 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12520 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12520 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12520 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12520,cell12520,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12520 ⟨51,by decide⟩).lower ∧ (cell12520 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12520 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12520 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12520 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12520 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12520 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12520,cell12520,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12520 ⟨52,by decide⟩).lower ∧ (cell12520 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12520 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12520 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12520 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12520 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12520 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12520,cell12520,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12520 i).lower ∧
    (cell12520 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12520 i).upper ≤ (0.532 : ℝ) ∧
    (cell12520 i).centre ≤ (0.1 : ℝ) ∧ (cell12520 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12520 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12520 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12520

/-! The local source numeric instances at 12520 have no network premises. -/
namespace BstLean.Part269.N12520
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12520)
open BstLean.Part268 (cell12520)

noncomputable def sourceNumerics12520 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12520 (cell12520 i)
      scalarRow12520.M scalarRow12520.H scalarRow12520.xi := by
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
    energy_allowance := scalarRow12520.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12520]
    centre_nonneg := (scalarRow12520.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D6.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12520])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12520
/-! Actual 12521 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12521
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12521 ≤ (1.036066536002 : ℝ) := by
  have hr : (111.897274318903 : ℝ) ≤ √(12521 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.897274318903 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12521 12521 (11 / 1000) ≤
    (0.008542541250 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12521) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.897274318903 : ℝ) ≤ √(12521 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12521)
  have hdiv : K / √(12521 : ℝ) ≤ K / 111.897274318903 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.897274318903 ≤ (0.008542541250 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12521.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12521 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12521 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12521 := gPlus_lower 12521
end BstLean.Part269.N12521

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12521
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036066536001 : ℝ) ≤ wn 12521 := by
  have hn : √(12521 : ℝ) ≤ 111.897274318904 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12521 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.897274318904 ≤ 2 / √(12521 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000255545220 : ℝ) ≤ rhoBar 12521 BstLean.Part154.csC ∧
    rhoBar 12521 BstLean.Part154.csC ≤ 0.000255545616 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036066536001 : ℝ) / (1.295212 * 12521) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036066536002 : ℝ) / (1.29521 * 12521) := by gcongr
      _ ≤ (0.000255545616 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12521 BstLean.Part154.csC) ≤ 0.001022247768 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12521 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12521 BstLean.Part154.csC) (piBar (rhoBar 12521 BstLean.Part154.csC)) ≤ 0.000195187598 ∧
    cc1 (rhoBar 12521 BstLean.Part154.csC) (piBar (rhoBar 12521 BstLean.Part154.csC)) ≤ 0.000124199137 ∧
    cc2 (rhoBar 12521 BstLean.Part154.csC) ≤ 0.000072098518 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12521 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12521 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12521 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12521 BstLean.Part154.csC * nuR (rhoBar 12521 BstLean.Part154.csC)) ≤ 0.000511107558 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000255545616 : ℝ) * 0.001022247768 := by gcongr
      _ ≤ (0.000511107558 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12521 BstLean.Part154.csC) * nuR (rhoBar 12521 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001022247768 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12521 BstLean.Part154.csC) * rhoBar 12521 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000255545616 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000255545616 / 2 + 0.399 * 0.001022247768 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000195187598 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000511107558 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124199137 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000255545616 / 1.414213562 := by gcongr
      _ ≤ (0.000072098518 : ℝ) := by norm_num

end BstLean.Part269.N12521

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12521
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12521 BstLean.Part154.csC) (piBar (rhoBar 12521 BstLean.Part154.csC)) ≤ 1.64528E-7 := by
  have hr0 : 0 ≤ rhoBar 12521 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12521 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12521 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12521 BstLean.Part154.csC) (piBar (rhoBar 12521 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12521 BstLean.Part154.csC) (piBar (rhoBar 12521 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12521 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000195187598 : ℝ) ^ 2 + 0.000124199137 ^ 2 + 3 * 0.000072098518 ^ 2 +
        2 * 0.797885 * 0.000195187598 * 0.000124199137 + 2 * 0.000195187598 * 0.000072098518 +
        4 * 0.797885 * 0.000124199137 * 0.000072098518 := by gcongr
    _ ≤ (1.64528E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12521 BstLean.Part154.csC Θ ≤ 0.002668208078 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12521 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12521 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12521 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12521 BstLean.Part154.csC) (piBar (rhoBar 12521 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12521 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036066536002 * 1.64528E-7 / (0.000255545220 : ℝ) := by gcongr
    _ ≤ 0.002668208078 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12521 BstLean.Part154.csC Θ ≤ 0.002961252742 + 0.000674211702 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12521 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12521 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12521 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036066536002 : ℝ) * ((2 * Θ * 0.000255545616 +
        (6863 / 10000) * 0.000255545616 * 12521 * 0.001022247768) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002961252742 + 0.000674211702 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12521 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12521 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12521 0.011 Θ ∧ gammaRatio 12521 0.011 Θ ≤ 0.000087849975 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12521 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036066536002 : ℝ) * 0.525 / ((1 - 0.011) * 12521) := by gcongr
      _ ≤ (0.000087849975 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12521 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12521 0.011 Θ) :=
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
    badAllowance 12521 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000774418828 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12521 BstLean.Part154.csC) 1.22 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 2 (rhoBar 12521 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12521 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12521 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12521 0.011 Θ) 1.12 ≤ 3.3895E-8 := by
    have he : (17.2 : ℝ) ≤ gap 1 (gammaRatio 12521 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12521 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12521 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12521 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12521 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036066536002 : ℝ) * 12521 *
        (2.7751E-8 / 1.1045361 + 3.3895E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000774418828 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12521 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003735671570 + 0.003342419780 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12521

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12521
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12521 BstLean.Part154.csC) (piBar (rhoBar 12521 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12521 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12521 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12521 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12521 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12521 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12521 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12521 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12521 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12521 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12521 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12521 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12521 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12521 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12521 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052862221342 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12521) ≤ 0.010672624408 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12521 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036066536002)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010672624408 + 2 * 0.737676 / 12521) := by gcongr
    _ ≤ (0.052862221342 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12521 12 ≤ 0.0015 := by
  exact BstLean.Part269.S6.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12521

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12521
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560495357655 : ℝ) ≤ plow 12521 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12521) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052997041955)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001400809241) : eMP 12521 0.011 xi bn ≤ 0.001205721169 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12521 : ℝ) * (1 - 0.011))) ≤ 0.000596138000 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001400809241 / (12521 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000596138000 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000596138000 : ℝ) + 3.141593 * 0.052997041955 / (12521 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001205721169 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052997041955)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001400809241) : PiBarMP 12521 12 0.011 xi bn ≤ 0.162411499457 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12521 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037427386244 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.280137490928 : ℝ) ≤ √((12521 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.897274318903 : ℝ) ≤ √(12521 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12521) ≤ 0.124510702764 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037427386244 + 0.052997041955 * 1.772454 / (2 * (111.280137490928 : ℝ))) * (1 + 0.001205721169) +
        8 / (12521 * 111.897274318903) + 0.124510702764 := by gcongr
    _ ≤ (0.162411499457 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052997041955)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001400809241) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283073085454) :
    parallelOracle 12521 0.011 xi bn cd ≤ 0.163416831989 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12521 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12521 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560495357655 : ℝ) ≤ plow 12521 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.897274318903 : ℝ) ≤ √(12521 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.283073085454 : ℝ) / (2 * 0.560495357655 * 111.897274318903)) * 0.162411499457 +
        0.283073085454 ^ 2 / (2 * 0.560495357655 * 111.897274318903) := by gcongr
    _ ≤ (0.163416831989 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052997041955) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001400809241)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283073085454) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12521 12521 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560495357655 : ℝ) ≤ plow 12521 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.897274318903 : ℝ) ≤ √(12521 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12521 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12521 Θ 1.22 ≤ 0.011851052746 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.897274318903 := by gcongr <;> linarith
      _ ≤ (0.011851052746 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12521 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12521 12521 0.011 ≤ 0.008542541250 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12521 12521 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12521 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12521 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12521 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12521 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163416831989 + 0.011851052746 + (0.008542541250 : ℝ) *
        (1 + 2 * (0.283073085454 + 0.011851052746) / (0.560495357655 * 111.897274318903))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12521]

end BstLean.Part269.N12521

/-! The original eight local profiles supply actual 12521 moment certificates. -/
namespace BstLean.Part269.N12521
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12521 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12521 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12521 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052997041955 ∧
    0 ≤ bN 12521 BstLean.Part154.csC (groupTheta g) ∧ bN 12521 BstLean.Part154.csC (groupTheta g) ≤ 0.001400809241 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12521 12521 0.011
      (momentAllowance 12521 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12521 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12521 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12521 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12521 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12521 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230210864112 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12521 0.011
      (momentAllowance 12521 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12521 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12521
/-! The actual computed-centre upper energy formula at 12521. -/
namespace BstLean.Part269.N12521
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12521

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12521
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12521)
open BstLean.Part268 (cell12521)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086030751358
  | 2 => 0.086983862620
  | 3 => 0.087936693686
  | 4 => 0.088891021433
  | 5 => 0.089848982340
  | 6 => 0.090813124212
  | 7 => 0.091786462468
  | 8 => 0.092772540978
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12521 12521 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12521 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003740909217 + 0.003348232271 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S6.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12521

/-! Actual upper energy certificates on all 43 source endpoints at 12521. -/
namespace BstLean.Part269.N12521
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12521)
open BstLean.Part268 (cell12521)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12521 (gMinus 12521) (1 - (cell12521 i).lower) ≤ 1 ∧
    energyUpper 12521 (gMinus 12521) (BstLean.Part211.gPlus 12521)
      (finiteEnergy 12521 12521 0.011) (1 - (cell12521 i).lower) ≤
      (cell12521 i).energy := by
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
      have E := BstLean.Part269.S6.uniformEnergy10 (n := 12521) (by norm_num)
        (q := 1 - (cell12521 ⟨10,by decide⟩).lower)
        (by norm_num [cell12521]) (by norm_num [cell12521])
      exact ⟨E.1,E.2.trans (by norm_num [cell12521])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy11 (n := 12521) (by norm_num)
        (q := 1 - (cell12521 ⟨11,by decide⟩).lower)
        (by norm_num [cell12521]) (by norm_num [cell12521])
      exact ⟨E.1,E.2.trans (by norm_num [cell12521])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy12 (n := 12521) (by norm_num)
        (q := 1 - (cell12521 ⟨12,by decide⟩).lower)
        (by norm_num [cell12521]) (by norm_num [cell12521])
      exact ⟨E.1,E.2.trans (by norm_num [cell12521])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy13 (n := 12521) (by norm_num)
        (q := 1 - (cell12521 ⟨13,by decide⟩).lower)
        (by norm_num [cell12521]) (by norm_num [cell12521])
      exact ⟨E.1,E.2.trans (by norm_num [cell12521])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy14 (n := 12521) (by norm_num)
        (q := 1 - (cell12521 ⟨14,by decide⟩).lower)
        (by norm_num [cell12521]) (by norm_num [cell12521])
      exact ⟨E.1,E.2.trans (by norm_num [cell12521])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy15 (n := 12521) (by norm_num)
        (q := 1 - (cell12521 ⟨15,by decide⟩).lower)
        (by norm_num [cell12521]) (by norm_num [cell12521])
      exact ⟨E.1,E.2.trans (by norm_num [cell12521])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy16 (n := 12521) (by norm_num)
        (q := 1 - (cell12521 ⟨16,by decide⟩).lower)
        (by norm_num [cell12521]) (by norm_num [cell12521])
      exact ⟨E.1,E.2.trans (by norm_num [cell12521])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy17 (n := 12521) (by norm_num)
        (q := 1 - (cell12521 ⟨17,by decide⟩).lower)
        (by norm_num [cell12521]) (by norm_num [cell12521])
      exact ⟨E.1,E.2.trans (by norm_num [cell12521])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy18 (n := 12521) (by norm_num)
        (q := 1 - (cell12521 ⟨18,by decide⟩).lower)
        (by norm_num [cell12521]) (by norm_num [cell12521])
      exact ⟨E.1,E.2.trans (by norm_num [cell12521])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy19 (n := 12521) (by norm_num)
        (q := 1 - (cell12521 ⟨19,by decide⟩).lower)
        (by norm_num [cell12521]) (by norm_num [cell12521])
      exact ⟨E.1,E.2.trans (by norm_num [cell12521])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy20 (n := 12521) (by norm_num)
        (q := 1 - (cell12521 ⟨20,by decide⟩).lower)
        (by norm_num [cell12521]) (by norm_num [cell12521])
      exact ⟨E.1,E.2.trans (by norm_num [cell12521])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy21 (n := 12521) (by norm_num)
        (q := 1 - (cell12521 ⟨21,by decide⟩).lower)
        (by norm_num [cell12521]) (by norm_num [cell12521])
      exact ⟨E.1,E.2.trans (by norm_num [cell12521])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy22 (n := 12521) (by norm_num)
        (q := 1 - (cell12521 ⟨22,by decide⟩).lower)
        (by norm_num [cell12521]) (by norm_num [cell12521])
      exact ⟨E.1,E.2.trans (by norm_num [cell12521])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy23 (n := 12521) (by norm_num)
        (q := 1 - (cell12521 ⟨23,by decide⟩).lower)
        (by norm_num [cell12521]) (by norm_num [cell12521])
      exact ⟨E.1,E.2.trans (by norm_num [cell12521])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy24 (n := 12521) (by norm_num)
        (q := 1 - (cell12521 ⟨24,by decide⟩).lower)
        (by norm_num [cell12521]) (by norm_num [cell12521])
      exact ⟨E.1,E.2.trans (by norm_num [cell12521])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy25 (n := 12521) (by norm_num)
        (q := 1 - (cell12521 ⟨25,by decide⟩).lower)
        (by norm_num [cell12521]) (by norm_num [cell12521])
      exact ⟨E.1,E.2.trans (by norm_num [cell12521])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy26 (n := 12521) (by norm_num)
        (q := 1 - (cell12521 ⟨26,by decide⟩).lower)
        (by norm_num [cell12521]) (by norm_num [cell12521])
      exact ⟨E.1,E.2.trans (by norm_num [cell12521])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy27 (n := 12521) (by norm_num)
        (q := 1 - (cell12521 ⟨27,by decide⟩).lower)
        (by norm_num [cell12521]) (by norm_num [cell12521])
      exact ⟨E.1,E.2.trans (by norm_num [cell12521])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy28 (n := 12521) (by norm_num)
        (q := 1 - (cell12521 ⟨28,by decide⟩).lower)
        (by norm_num [cell12521]) (by norm_num [cell12521])
      exact ⟨E.1,E.2.trans (by norm_num [cell12521])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy29 (n := 12521) (by norm_num)
        (q := 1 - (cell12521 ⟨29,by decide⟩).lower)
        (by norm_num [cell12521]) (by norm_num [cell12521])
      exact ⟨E.1,E.2.trans (by norm_num [cell12521])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy30 (n := 12521) (by norm_num)
        (q := 1 - (cell12521 ⟨30,by decide⟩).lower)
        (by norm_num [cell12521]) (by norm_num [cell12521])
      exact ⟨E.1,E.2.trans (by norm_num [cell12521])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy31 (n := 12521) (by norm_num)
        (q := 1 - (cell12521 ⟨31,by decide⟩).lower)
        (by norm_num [cell12521]) (by norm_num [cell12521])
      exact ⟨E.1,E.2.trans (by norm_num [cell12521])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy32 (n := 12521) (by norm_num)
        (q := 1 - (cell12521 ⟨32,by decide⟩).lower)
        (by norm_num [cell12521]) (by norm_num [cell12521])
      exact ⟨E.1,E.2.trans (by norm_num [cell12521])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy33 (n := 12521) (by norm_num)
        (q := 1 - (cell12521 ⟨33,by decide⟩).lower)
        (by norm_num [cell12521]) (by norm_num [cell12521])
      exact ⟨E.1,E.2.trans (by norm_num [cell12521])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy34 (n := 12521) (by norm_num)
        (q := 1 - (cell12521 ⟨34,by decide⟩).lower)
        (by norm_num [cell12521]) (by norm_num [cell12521])
      exact ⟨E.1,E.2.trans (by norm_num [cell12521])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy35 (n := 12521) (by norm_num)
        (q := 1 - (cell12521 ⟨35,by decide⟩).lower)
        (by norm_num [cell12521]) (by norm_num [cell12521])
      exact ⟨E.1,E.2.trans (by norm_num [cell12521])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy36 (n := 12521) (by norm_num)
        (q := 1 - (cell12521 ⟨36,by decide⟩).lower)
        (by norm_num [cell12521]) (by norm_num [cell12521])
      exact ⟨E.1,E.2.trans (by norm_num [cell12521])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy37 (n := 12521) (by norm_num)
        (q := 1 - (cell12521 ⟨37,by decide⟩).lower)
        (by norm_num [cell12521]) (by norm_num [cell12521])
      exact ⟨E.1,E.2.trans (by norm_num [cell12521])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy38 (n := 12521) (by norm_num)
        (q := 1 - (cell12521 ⟨38,by decide⟩).lower)
        (by norm_num [cell12521]) (by norm_num [cell12521])
      exact ⟨E.1,E.2.trans (by norm_num [cell12521])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy39 (n := 12521) (by norm_num)
        (q := 1 - (cell12521 ⟨39,by decide⟩).lower)
        (by norm_num [cell12521]) (by norm_num [cell12521])
      exact ⟨E.1,E.2.trans (by norm_num [cell12521])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy40 (n := 12521) (by norm_num)
        (q := 1 - (cell12521 ⟨40,by decide⟩).lower)
        (by norm_num [cell12521]) (by norm_num [cell12521])
      exact ⟨E.1,E.2.trans (by norm_num [cell12521])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy41 (n := 12521) (by norm_num)
        (q := 1 - (cell12521 ⟨41,by decide⟩).lower)
        (by norm_num [cell12521]) (by norm_num [cell12521])
      exact ⟨E.1,E.2.trans (by norm_num [cell12521])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy42 (n := 12521) (by norm_num)
        (q := 1 - (cell12521 ⟨42,by decide⟩).lower)
        (by norm_num [cell12521]) (by norm_num [cell12521])
      exact ⟨E.1,E.2.trans (by norm_num [cell12521])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy43 (n := 12521) (by norm_num)
        (q := 1 - (cell12521 ⟨43,by decide⟩).lower)
        (by norm_num [cell12521]) (by norm_num [cell12521])
      exact ⟨E.1,E.2.trans (by norm_num [cell12521])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy44 (n := 12521) (by norm_num)
        (q := 1 - (cell12521 ⟨44,by decide⟩).lower)
        (by norm_num [cell12521]) (by norm_num [cell12521])
      exact ⟨E.1,E.2.trans (by norm_num [cell12521])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy45 (n := 12521) (by norm_num)
        (q := 1 - (cell12521 ⟨45,by decide⟩).lower)
        (by norm_num [cell12521]) (by norm_num [cell12521])
      exact ⟨E.1,E.2.trans (by norm_num [cell12521])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy46 (n := 12521) (by norm_num)
        (q := 1 - (cell12521 ⟨46,by decide⟩).lower)
        (by norm_num [cell12521]) (by norm_num [cell12521])
      exact ⟨E.1,E.2.trans (by norm_num [cell12521])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy47 (n := 12521) (by norm_num)
        (q := 1 - (cell12521 ⟨47,by decide⟩).lower)
        (by norm_num [cell12521]) (by norm_num [cell12521])
      exact ⟨E.1,E.2.trans (by norm_num [cell12521])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy48 (n := 12521) (by norm_num)
        (q := 1 - (cell12521 ⟨48,by decide⟩).lower)
        (by norm_num [cell12521]) (by norm_num [cell12521])
      exact ⟨E.1,E.2.trans (by norm_num [cell12521])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy49 (n := 12521) (by norm_num)
        (q := 1 - (cell12521 ⟨49,by decide⟩).lower)
        (by norm_num [cell12521]) (by norm_num [cell12521])
      exact ⟨E.1,E.2.trans (by norm_num [cell12521])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy50 (n := 12521) (by norm_num)
        (q := 1 - (cell12521 ⟨50,by decide⟩).lower)
        (by norm_num [cell12521]) (by norm_num [cell12521])
      exact ⟨E.1,E.2.trans (by norm_num [cell12521])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy51 (n := 12521) (by norm_num)
        (q := 1 - (cell12521 ⟨51,by decide⟩).lower)
        (by norm_num [cell12521]) (by norm_num [cell12521])
      exact ⟨E.1,E.2.trans (by norm_num [cell12521])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy52 (n := 12521) (by norm_num)
        (q := 1 - (cell12521 ⟨52,by decide⟩).lower)
        (by norm_num [cell12521]) (by norm_num [cell12521])
      exact ⟨E.1,E.2.trans (by norm_num [cell12521])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12521

/-! Source-cell containment and simple scalar guards at 12521. -/
namespace BstLean.Part269.N12521
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12521)
open BstLean.Part268 (cell12521)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12521 ⟨10,by decide⟩).lower ∧ (cell12521 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12521 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12521 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12521 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12521 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12521 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12521,cell12521,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12521 ⟨11,by decide⟩).lower ∧ (cell12521 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12521 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12521 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12521 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12521 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12521 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12521,cell12521,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12521 ⟨12,by decide⟩).lower ∧ (cell12521 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12521 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12521 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12521 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12521 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12521 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12521,cell12521,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12521 ⟨13,by decide⟩).lower ∧ (cell12521 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12521 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12521 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12521 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12521 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12521 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12521,cell12521,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12521 ⟨14,by decide⟩).lower ∧ (cell12521 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12521 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12521 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12521 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12521 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12521 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12521,cell12521,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12521 ⟨15,by decide⟩).lower ∧ (cell12521 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12521 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12521 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12521 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12521 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12521 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12521,cell12521,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12521 ⟨16,by decide⟩).lower ∧ (cell12521 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12521 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12521 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12521 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12521 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12521 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12521,cell12521,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12521 ⟨17,by decide⟩).lower ∧ (cell12521 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12521 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12521 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12521 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12521 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12521 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12521,cell12521,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12521 ⟨18,by decide⟩).lower ∧ (cell12521 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12521 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12521 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12521 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12521 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12521 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12521,cell12521,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12521 ⟨19,by decide⟩).lower ∧ (cell12521 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12521 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12521 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12521 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12521 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12521 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12521,cell12521,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12521 ⟨20,by decide⟩).lower ∧ (cell12521 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12521 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12521 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12521 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12521 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12521 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12521,cell12521,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12521 ⟨21,by decide⟩).lower ∧ (cell12521 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12521 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12521 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12521 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12521 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12521 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12521,cell12521,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12521 ⟨22,by decide⟩).lower ∧ (cell12521 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12521 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12521 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12521 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12521 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12521 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12521,cell12521,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12521 ⟨23,by decide⟩).lower ∧ (cell12521 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12521 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12521 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12521 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12521 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12521 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12521,cell12521,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12521 ⟨24,by decide⟩).lower ∧ (cell12521 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12521 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12521 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12521 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12521 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12521 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12521,cell12521,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12521 ⟨25,by decide⟩).lower ∧ (cell12521 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12521 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12521 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12521 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12521 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12521 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12521,cell12521,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12521 ⟨26,by decide⟩).lower ∧ (cell12521 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12521 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12521 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12521 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12521 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12521 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12521,cell12521,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12521 ⟨27,by decide⟩).lower ∧ (cell12521 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12521 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12521 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12521 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12521 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12521 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12521,cell12521,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12521 ⟨28,by decide⟩).lower ∧ (cell12521 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12521 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12521 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12521 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12521 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12521 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12521,cell12521,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12521 ⟨29,by decide⟩).lower ∧ (cell12521 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12521 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12521 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12521 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12521 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12521 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12521,cell12521,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12521 ⟨30,by decide⟩).lower ∧ (cell12521 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12521 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12521 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12521 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12521 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12521 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12521,cell12521,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12521 ⟨31,by decide⟩).lower ∧ (cell12521 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12521 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12521 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12521 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12521 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12521 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12521,cell12521,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12521 ⟨32,by decide⟩).lower ∧ (cell12521 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12521 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12521 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12521 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12521 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12521 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12521,cell12521,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12521 ⟨33,by decide⟩).lower ∧ (cell12521 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12521 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12521 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12521 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12521 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12521 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12521,cell12521,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12521 ⟨34,by decide⟩).lower ∧ (cell12521 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12521 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12521 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12521 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12521 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12521 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12521,cell12521,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12521 ⟨35,by decide⟩).lower ∧ (cell12521 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12521 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12521 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12521 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12521 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12521 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12521,cell12521,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12521 ⟨36,by decide⟩).lower ∧ (cell12521 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12521 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12521 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12521 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12521 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12521 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12521,cell12521,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12521 ⟨37,by decide⟩).lower ∧ (cell12521 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12521 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12521 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12521 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12521 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12521 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12521,cell12521,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12521 ⟨38,by decide⟩).lower ∧ (cell12521 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12521 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12521 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12521 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12521 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12521 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12521,cell12521,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12521 ⟨39,by decide⟩).lower ∧ (cell12521 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12521 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12521 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12521 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12521 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12521 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12521,cell12521,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12521 ⟨40,by decide⟩).lower ∧ (cell12521 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12521 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12521 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12521 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12521 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12521 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12521,cell12521,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12521 ⟨41,by decide⟩).lower ∧ (cell12521 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12521 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12521 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12521 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12521 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12521 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12521,cell12521,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12521 ⟨42,by decide⟩).lower ∧ (cell12521 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12521 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12521 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12521 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12521 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12521 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12521,cell12521,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12521 ⟨43,by decide⟩).lower ∧ (cell12521 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12521 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12521 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12521 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12521 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12521 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12521,cell12521,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12521 ⟨44,by decide⟩).lower ∧ (cell12521 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12521 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12521 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12521 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12521 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12521 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12521,cell12521,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12521 ⟨45,by decide⟩).lower ∧ (cell12521 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12521 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12521 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12521 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12521 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12521 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12521,cell12521,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12521 ⟨46,by decide⟩).lower ∧ (cell12521 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12521 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12521 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12521 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12521 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12521 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12521,cell12521,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12521 ⟨47,by decide⟩).lower ∧ (cell12521 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12521 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12521 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12521 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12521 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12521 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12521,cell12521,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12521 ⟨48,by decide⟩).lower ∧ (cell12521 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12521 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12521 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12521 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12521 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12521 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12521,cell12521,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12521 ⟨49,by decide⟩).lower ∧ (cell12521 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12521 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12521 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12521 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12521 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12521 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12521,cell12521,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12521 ⟨50,by decide⟩).lower ∧ (cell12521 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12521 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12521 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12521 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12521 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12521 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12521,cell12521,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12521 ⟨51,by decide⟩).lower ∧ (cell12521 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12521 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12521 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12521 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12521 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12521 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12521,cell12521,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12521 ⟨52,by decide⟩).lower ∧ (cell12521 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12521 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12521 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12521 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12521 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12521 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12521,cell12521,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12521 i).lower ∧
    (cell12521 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12521 i).upper ≤ (0.532 : ℝ) ∧
    (cell12521 i).centre ≤ (0.1 : ℝ) ∧ (cell12521 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12521 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12521 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12521

/-! The local source numeric instances at 12521 have no network premises. -/
namespace BstLean.Part269.N12521
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12521)
open BstLean.Part268 (cell12521)

noncomputable def sourceNumerics12521 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12521 (cell12521 i)
      scalarRow12521.M scalarRow12521.H scalarRow12521.xi := by
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
    energy_allowance := scalarRow12521.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12521]
    centre_nonneg := (scalarRow12521.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D6.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12521])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12521
/-! Actual 12522 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12522
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12522 ≤ (1.036065083091 : ℝ) := by
  have hr : (111.901742613777 : ℝ) ≤ √(12522 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.901742613777 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12522 12522 (11 / 1000) ≤
    (0.008542200139 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12522) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.901742613777 : ℝ) ≤ √(12522 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12522)
  have hdiv : K / √(12522 : ℝ) ≤ K / 111.901742613777 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.901742613777 ≤ (0.008542200139 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12522.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12522 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12522 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12522 := gPlus_lower 12522
end BstLean.Part269.N12522

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12522
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036065083090 : ℝ) ≤ wn 12522 := by
  have hn : √(12522 : ℝ) ≤ 111.901742613778 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12522 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.901742613778 ≤ 2 / √(12522 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000255524454 : ℝ) ≤ rhoBar 12522 BstLean.Part154.csC ∧
    rhoBar 12522 BstLean.Part154.csC ≤ 0.000255524850 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036065083090 : ℝ) / (1.295212 * 12522) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036065083091 : ℝ) / (1.29521 * 12522) := by gcongr
      _ ≤ (0.000255524850 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12522 BstLean.Part154.csC) ≤ 0.001022164693 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12522 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12522 BstLean.Part154.csC) (piBar (rhoBar 12522 BstLean.Part154.csC)) ≤ 0.000195171736 ∧
    cc1 (rhoBar 12522 BstLean.Part154.csC) (piBar (rhoBar 12522 BstLean.Part154.csC)) ≤ 0.000124189044 ∧
    cc2 (rhoBar 12522 BstLean.Part154.csC) ≤ 0.000072092659 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12522 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12522 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12522 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12522 BstLean.Part154.csC * nuR (rhoBar 12522 BstLean.Part154.csC)) ≤ 0.000511066023 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000255524850 : ℝ) * 0.001022164693 := by gcongr
      _ ≤ (0.000511066023 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12522 BstLean.Part154.csC) * nuR (rhoBar 12522 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001022164693 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12522 BstLean.Part154.csC) * rhoBar 12522 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000255524850 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000255524850 / 2 + 0.399 * 0.001022164693 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000195171736 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000511066023 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124189044 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000255524850 / 1.414213562 := by gcongr
      _ ≤ (0.000072092659 : ℝ) := by norm_num

end BstLean.Part269.N12522

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12522
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12522 BstLean.Part154.csC) (piBar (rhoBar 12522 BstLean.Part154.csC)) ≤ 1.64501E-7 := by
  have hr0 : 0 ≤ rhoBar 12522 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12522 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12522 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12522 BstLean.Part154.csC) (piBar (rhoBar 12522 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12522 BstLean.Part154.csC) (piBar (rhoBar 12522 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12522 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000195171736 : ℝ) ^ 2 + 0.000124189044 ^ 2 + 3 * 0.000072092659 ^ 2 +
        2 * 0.797885 * 0.000195171736 * 0.000124189044 + 2 * 0.000195171736 * 0.000072092659 +
        4 * 0.797885 * 0.000124189044 * 0.000072092659 := by gcongr
    _ ≤ (1.64501E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12522 BstLean.Part154.csC Θ ≤ 0.002667983273 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12522 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12522 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12522 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12522 BstLean.Part154.csC) (piBar (rhoBar 12522 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12522 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036065083091 * 1.64501E-7 / (0.000255524454 : ℝ) := by gcongr
    _ ≤ 0.002667983273 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12522 BstLean.Part154.csC Θ ≤ 0.002961003786 + 0.000674155970 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12522 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12522 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12522 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036065083091 : ℝ) * ((2 * Θ * 0.000255524850 +
        (6863 / 10000) * 0.000255524850 * 12522 * 0.001022164693) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002961003786 + 0.000674155970 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12522 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12522 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12522 0.011 Θ ∧ gammaRatio 12522 0.011 Θ ≤ 0.000087842836 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12522 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036065083091 : ℝ) * 0.525 / ((1 - 0.011) * 12522) := by gcongr
      _ ≤ (0.000087842836 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12522 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12522 0.011 Θ) :=
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
    badAllowance 12522 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000774418828 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12522 BstLean.Part154.csC) 1.22 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 2 (rhoBar 12522 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12522 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12522 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12522 0.011 Θ) 1.12 ≤ 3.3895E-8 := by
    have he : (17.2 : ℝ) ≤ gap 1 (gammaRatio 12522 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12522 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12522 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12522 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12522 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036065083091 : ℝ) * 12522 *
        (2.7751E-8 / 1.1045361 + 3.3895E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000774418828 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12522 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003735422614 + 0.003342139243 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12522

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12522
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12522 BstLean.Part154.csC) (piBar (rhoBar 12522 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12522 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12522 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12522 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12522 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12522 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12522 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12522 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12522 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12522 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12522 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12522 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12522 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12522 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12522 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052860087479 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12522) ≤ 0.010672198245 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12522 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036065083091)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010672198245 + 2 * 0.737676 / 12522) := by gcongr
    _ ≤ (0.052860087479 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12522 12 ≤ 0.0015 := by
  exact BstLean.Part269.S6.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12522

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12522
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560495404176 : ℝ) ≤ plow 12522 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12522) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052996645717)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001400691219) : eMP 12522 0.011 xi bn ≤ 0.001205622161 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12522 : ℝ) * (1 - 0.011))) ≤ 0.000596089083 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001400691219 / (12522 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000596089083 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000596089083 : ℝ) + 3.141593 * 0.052996645717 / (12522 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001205622161 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052996645717)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001400691219) : PiBarMP 12522 12 0.011 xi bn ≤ 0.162404924601 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12522 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037425809531 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.284581142222 : ℝ) ≤ √((12522 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.901742613777 : ℝ) ≤ √(12522 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12522) ≤ 0.124505730987 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037425809531 + 0.052996645717 * 1.772454 / (2 * (111.284581142222 : ℝ))) * (1 + 0.001205622161) +
        8 / (12522 * 111.901742613777) + 0.124505730987 := by gcongr
    _ ≤ (0.162404924601 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052996645717)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001400691219) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283070090992) :
    parallelOracle 12522 0.011 xi bn cd ≤ 0.163410184678 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12522 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12522 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560495404176 : ℝ) ≤ plow 12522 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.901742613777 : ℝ) ≤ √(12522 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.283070090992 : ℝ) / (2 * 0.560495404176 * 111.901742613777)) * 0.162404924601 +
        0.283070090992 ^ 2 / (2 * 0.560495404176 * 111.901742613777) := by gcongr
    _ ≤ (0.163410184678 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052996645717) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001400691219)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283070090992) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12522 12522 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560495404176 : ℝ) ≤ plow 12522 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.901742613777 : ℝ) ≤ √(12522 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12522 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12522 Θ 1.22 ≤ 0.011850579527 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.901742613777 := by gcongr <;> linarith
      _ ≤ (0.011850579527 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12522 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12522 12522 0.011 ≤ 0.008542200139 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12522 12522 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12522 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12522 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12522 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12522 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163410184678 + 0.011850579527 + (0.008542200139 : ℝ) *
        (1 + 2 * (0.283070090992 + 0.011850579527) / (0.560495404176 * 111.901742613777))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12522]

end BstLean.Part269.N12522

/-! The original eight local profiles supply actual 12522 moment certificates. -/
namespace BstLean.Part269.N12522
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12522 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12522 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12522 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052996645717 ∧
    0 ≤ bN 12522 BstLean.Part154.csC (groupTheta g) ∧ bN 12522 BstLean.Part154.csC (groupTheta g) ≤ 0.001400691219 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12522 12522 0.011
      (momentAllowance 12522 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12522 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12522 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12522 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12522 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12522 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230210003513 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12522 0.011
      (momentAllowance 12522 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12522 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12522
/-! The actual computed-centre upper energy formula at 12522. -/
namespace BstLean.Part269.N12522
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12522

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12522
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12522)
open BstLean.Part268 (cell12522)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086027622662
  | 2 => 0.086980671405
  | 3 => 0.087933430039
  | 4 => 0.088887673221
  | 5 => 0.089845534824
  | 6 => 0.090809559626
  | 7 => 0.091782759540
  | 8 => 0.092768674408
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12522 12522 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12522 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003740909217 + 0.003348232271 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S6.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12522

/-! Actual upper energy certificates on all 43 source endpoints at 12522. -/
namespace BstLean.Part269.N12522
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12522)
open BstLean.Part268 (cell12522)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12522 (gMinus 12522) (1 - (cell12522 i).lower) ≤ 1 ∧
    energyUpper 12522 (gMinus 12522) (BstLean.Part211.gPlus 12522)
      (finiteEnergy 12522 12522 0.011) (1 - (cell12522 i).lower) ≤
      (cell12522 i).energy := by
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
      have E := BstLean.Part269.S6.uniformEnergy10 (n := 12522) (by norm_num)
        (q := 1 - (cell12522 ⟨10,by decide⟩).lower)
        (by norm_num [cell12522]) (by norm_num [cell12522])
      exact ⟨E.1,E.2.trans (by norm_num [cell12522])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy11 (n := 12522) (by norm_num)
        (q := 1 - (cell12522 ⟨11,by decide⟩).lower)
        (by norm_num [cell12522]) (by norm_num [cell12522])
      exact ⟨E.1,E.2.trans (by norm_num [cell12522])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy12 (n := 12522) (by norm_num)
        (q := 1 - (cell12522 ⟨12,by decide⟩).lower)
        (by norm_num [cell12522]) (by norm_num [cell12522])
      exact ⟨E.1,E.2.trans (by norm_num [cell12522])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy13 (n := 12522) (by norm_num)
        (q := 1 - (cell12522 ⟨13,by decide⟩).lower)
        (by norm_num [cell12522]) (by norm_num [cell12522])
      exact ⟨E.1,E.2.trans (by norm_num [cell12522])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy14 (n := 12522) (by norm_num)
        (q := 1 - (cell12522 ⟨14,by decide⟩).lower)
        (by norm_num [cell12522]) (by norm_num [cell12522])
      exact ⟨E.1,E.2.trans (by norm_num [cell12522])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy15 (n := 12522) (by norm_num)
        (q := 1 - (cell12522 ⟨15,by decide⟩).lower)
        (by norm_num [cell12522]) (by norm_num [cell12522])
      exact ⟨E.1,E.2.trans (by norm_num [cell12522])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy16 (n := 12522) (by norm_num)
        (q := 1 - (cell12522 ⟨16,by decide⟩).lower)
        (by norm_num [cell12522]) (by norm_num [cell12522])
      exact ⟨E.1,E.2.trans (by norm_num [cell12522])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy17 (n := 12522) (by norm_num)
        (q := 1 - (cell12522 ⟨17,by decide⟩).lower)
        (by norm_num [cell12522]) (by norm_num [cell12522])
      exact ⟨E.1,E.2.trans (by norm_num [cell12522])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy18 (n := 12522) (by norm_num)
        (q := 1 - (cell12522 ⟨18,by decide⟩).lower)
        (by norm_num [cell12522]) (by norm_num [cell12522])
      exact ⟨E.1,E.2.trans (by norm_num [cell12522])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy19 (n := 12522) (by norm_num)
        (q := 1 - (cell12522 ⟨19,by decide⟩).lower)
        (by norm_num [cell12522]) (by norm_num [cell12522])
      exact ⟨E.1,E.2.trans (by norm_num [cell12522])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy20 (n := 12522) (by norm_num)
        (q := 1 - (cell12522 ⟨20,by decide⟩).lower)
        (by norm_num [cell12522]) (by norm_num [cell12522])
      exact ⟨E.1,E.2.trans (by norm_num [cell12522])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy21 (n := 12522) (by norm_num)
        (q := 1 - (cell12522 ⟨21,by decide⟩).lower)
        (by norm_num [cell12522]) (by norm_num [cell12522])
      exact ⟨E.1,E.2.trans (by norm_num [cell12522])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy22 (n := 12522) (by norm_num)
        (q := 1 - (cell12522 ⟨22,by decide⟩).lower)
        (by norm_num [cell12522]) (by norm_num [cell12522])
      exact ⟨E.1,E.2.trans (by norm_num [cell12522])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy23 (n := 12522) (by norm_num)
        (q := 1 - (cell12522 ⟨23,by decide⟩).lower)
        (by norm_num [cell12522]) (by norm_num [cell12522])
      exact ⟨E.1,E.2.trans (by norm_num [cell12522])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy24 (n := 12522) (by norm_num)
        (q := 1 - (cell12522 ⟨24,by decide⟩).lower)
        (by norm_num [cell12522]) (by norm_num [cell12522])
      exact ⟨E.1,E.2.trans (by norm_num [cell12522])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy25 (n := 12522) (by norm_num)
        (q := 1 - (cell12522 ⟨25,by decide⟩).lower)
        (by norm_num [cell12522]) (by norm_num [cell12522])
      exact ⟨E.1,E.2.trans (by norm_num [cell12522])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy26 (n := 12522) (by norm_num)
        (q := 1 - (cell12522 ⟨26,by decide⟩).lower)
        (by norm_num [cell12522]) (by norm_num [cell12522])
      exact ⟨E.1,E.2.trans (by norm_num [cell12522])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy27 (n := 12522) (by norm_num)
        (q := 1 - (cell12522 ⟨27,by decide⟩).lower)
        (by norm_num [cell12522]) (by norm_num [cell12522])
      exact ⟨E.1,E.2.trans (by norm_num [cell12522])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy28 (n := 12522) (by norm_num)
        (q := 1 - (cell12522 ⟨28,by decide⟩).lower)
        (by norm_num [cell12522]) (by norm_num [cell12522])
      exact ⟨E.1,E.2.trans (by norm_num [cell12522])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy29 (n := 12522) (by norm_num)
        (q := 1 - (cell12522 ⟨29,by decide⟩).lower)
        (by norm_num [cell12522]) (by norm_num [cell12522])
      exact ⟨E.1,E.2.trans (by norm_num [cell12522])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy30 (n := 12522) (by norm_num)
        (q := 1 - (cell12522 ⟨30,by decide⟩).lower)
        (by norm_num [cell12522]) (by norm_num [cell12522])
      exact ⟨E.1,E.2.trans (by norm_num [cell12522])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy31 (n := 12522) (by norm_num)
        (q := 1 - (cell12522 ⟨31,by decide⟩).lower)
        (by norm_num [cell12522]) (by norm_num [cell12522])
      exact ⟨E.1,E.2.trans (by norm_num [cell12522])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy32 (n := 12522) (by norm_num)
        (q := 1 - (cell12522 ⟨32,by decide⟩).lower)
        (by norm_num [cell12522]) (by norm_num [cell12522])
      exact ⟨E.1,E.2.trans (by norm_num [cell12522])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy33 (n := 12522) (by norm_num)
        (q := 1 - (cell12522 ⟨33,by decide⟩).lower)
        (by norm_num [cell12522]) (by norm_num [cell12522])
      exact ⟨E.1,E.2.trans (by norm_num [cell12522])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy34 (n := 12522) (by norm_num)
        (q := 1 - (cell12522 ⟨34,by decide⟩).lower)
        (by norm_num [cell12522]) (by norm_num [cell12522])
      exact ⟨E.1,E.2.trans (by norm_num [cell12522])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy35 (n := 12522) (by norm_num)
        (q := 1 - (cell12522 ⟨35,by decide⟩).lower)
        (by norm_num [cell12522]) (by norm_num [cell12522])
      exact ⟨E.1,E.2.trans (by norm_num [cell12522])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy36 (n := 12522) (by norm_num)
        (q := 1 - (cell12522 ⟨36,by decide⟩).lower)
        (by norm_num [cell12522]) (by norm_num [cell12522])
      exact ⟨E.1,E.2.trans (by norm_num [cell12522])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy37 (n := 12522) (by norm_num)
        (q := 1 - (cell12522 ⟨37,by decide⟩).lower)
        (by norm_num [cell12522]) (by norm_num [cell12522])
      exact ⟨E.1,E.2.trans (by norm_num [cell12522])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy38 (n := 12522) (by norm_num)
        (q := 1 - (cell12522 ⟨38,by decide⟩).lower)
        (by norm_num [cell12522]) (by norm_num [cell12522])
      exact ⟨E.1,E.2.trans (by norm_num [cell12522])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy39 (n := 12522) (by norm_num)
        (q := 1 - (cell12522 ⟨39,by decide⟩).lower)
        (by norm_num [cell12522]) (by norm_num [cell12522])
      exact ⟨E.1,E.2.trans (by norm_num [cell12522])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy40 (n := 12522) (by norm_num)
        (q := 1 - (cell12522 ⟨40,by decide⟩).lower)
        (by norm_num [cell12522]) (by norm_num [cell12522])
      exact ⟨E.1,E.2.trans (by norm_num [cell12522])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy41 (n := 12522) (by norm_num)
        (q := 1 - (cell12522 ⟨41,by decide⟩).lower)
        (by norm_num [cell12522]) (by norm_num [cell12522])
      exact ⟨E.1,E.2.trans (by norm_num [cell12522])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy42 (n := 12522) (by norm_num)
        (q := 1 - (cell12522 ⟨42,by decide⟩).lower)
        (by norm_num [cell12522]) (by norm_num [cell12522])
      exact ⟨E.1,E.2.trans (by norm_num [cell12522])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy43 (n := 12522) (by norm_num)
        (q := 1 - (cell12522 ⟨43,by decide⟩).lower)
        (by norm_num [cell12522]) (by norm_num [cell12522])
      exact ⟨E.1,E.2.trans (by norm_num [cell12522])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy44 (n := 12522) (by norm_num)
        (q := 1 - (cell12522 ⟨44,by decide⟩).lower)
        (by norm_num [cell12522]) (by norm_num [cell12522])
      exact ⟨E.1,E.2.trans (by norm_num [cell12522])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy45 (n := 12522) (by norm_num)
        (q := 1 - (cell12522 ⟨45,by decide⟩).lower)
        (by norm_num [cell12522]) (by norm_num [cell12522])
      exact ⟨E.1,E.2.trans (by norm_num [cell12522])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy46 (n := 12522) (by norm_num)
        (q := 1 - (cell12522 ⟨46,by decide⟩).lower)
        (by norm_num [cell12522]) (by norm_num [cell12522])
      exact ⟨E.1,E.2.trans (by norm_num [cell12522])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy47 (n := 12522) (by norm_num)
        (q := 1 - (cell12522 ⟨47,by decide⟩).lower)
        (by norm_num [cell12522]) (by norm_num [cell12522])
      exact ⟨E.1,E.2.trans (by norm_num [cell12522])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy48 (n := 12522) (by norm_num)
        (q := 1 - (cell12522 ⟨48,by decide⟩).lower)
        (by norm_num [cell12522]) (by norm_num [cell12522])
      exact ⟨E.1,E.2.trans (by norm_num [cell12522])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy49 (n := 12522) (by norm_num)
        (q := 1 - (cell12522 ⟨49,by decide⟩).lower)
        (by norm_num [cell12522]) (by norm_num [cell12522])
      exact ⟨E.1,E.2.trans (by norm_num [cell12522])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy50 (n := 12522) (by norm_num)
        (q := 1 - (cell12522 ⟨50,by decide⟩).lower)
        (by norm_num [cell12522]) (by norm_num [cell12522])
      exact ⟨E.1,E.2.trans (by norm_num [cell12522])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy51 (n := 12522) (by norm_num)
        (q := 1 - (cell12522 ⟨51,by decide⟩).lower)
        (by norm_num [cell12522]) (by norm_num [cell12522])
      exact ⟨E.1,E.2.trans (by norm_num [cell12522])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy52 (n := 12522) (by norm_num)
        (q := 1 - (cell12522 ⟨52,by decide⟩).lower)
        (by norm_num [cell12522]) (by norm_num [cell12522])
      exact ⟨E.1,E.2.trans (by norm_num [cell12522])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12522

/-! Source-cell containment and simple scalar guards at 12522. -/
namespace BstLean.Part269.N12522
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12522)
open BstLean.Part268 (cell12522)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12522 ⟨10,by decide⟩).lower ∧ (cell12522 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12522 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12522 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12522 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12522 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12522 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12522,cell12522,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12522 ⟨11,by decide⟩).lower ∧ (cell12522 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12522 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12522 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12522 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12522 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12522 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12522,cell12522,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12522 ⟨12,by decide⟩).lower ∧ (cell12522 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12522 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12522 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12522 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12522 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12522 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12522,cell12522,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12522 ⟨13,by decide⟩).lower ∧ (cell12522 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12522 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12522 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12522 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12522 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12522 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12522,cell12522,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12522 ⟨14,by decide⟩).lower ∧ (cell12522 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12522 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12522 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12522 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12522 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12522 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12522,cell12522,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12522 ⟨15,by decide⟩).lower ∧ (cell12522 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12522 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12522 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12522 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12522 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12522 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12522,cell12522,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12522 ⟨16,by decide⟩).lower ∧ (cell12522 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12522 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12522 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12522 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12522 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12522 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12522,cell12522,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12522 ⟨17,by decide⟩).lower ∧ (cell12522 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12522 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12522 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12522 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12522 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12522 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12522,cell12522,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12522 ⟨18,by decide⟩).lower ∧ (cell12522 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12522 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12522 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12522 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12522 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12522 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12522,cell12522,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12522 ⟨19,by decide⟩).lower ∧ (cell12522 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12522 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12522 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12522 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12522 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12522 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12522,cell12522,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12522 ⟨20,by decide⟩).lower ∧ (cell12522 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12522 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12522 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12522 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12522 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12522 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12522,cell12522,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12522 ⟨21,by decide⟩).lower ∧ (cell12522 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12522 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12522 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12522 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12522 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12522 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12522,cell12522,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12522 ⟨22,by decide⟩).lower ∧ (cell12522 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12522 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12522 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12522 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12522 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12522 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12522,cell12522,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12522 ⟨23,by decide⟩).lower ∧ (cell12522 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12522 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12522 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12522 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12522 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12522 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12522,cell12522,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12522 ⟨24,by decide⟩).lower ∧ (cell12522 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12522 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12522 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12522 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12522 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12522 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12522,cell12522,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12522 ⟨25,by decide⟩).lower ∧ (cell12522 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12522 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12522 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12522 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12522 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12522 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12522,cell12522,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12522 ⟨26,by decide⟩).lower ∧ (cell12522 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12522 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12522 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12522 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12522 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12522 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12522,cell12522,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12522 ⟨27,by decide⟩).lower ∧ (cell12522 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12522 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12522 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12522 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12522 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12522 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12522,cell12522,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12522 ⟨28,by decide⟩).lower ∧ (cell12522 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12522 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12522 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12522 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12522 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12522 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12522,cell12522,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12522 ⟨29,by decide⟩).lower ∧ (cell12522 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12522 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12522 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12522 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12522 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12522 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12522,cell12522,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12522 ⟨30,by decide⟩).lower ∧ (cell12522 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12522 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12522 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12522 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12522 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12522 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12522,cell12522,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12522 ⟨31,by decide⟩).lower ∧ (cell12522 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12522 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12522 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12522 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12522 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12522 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12522,cell12522,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12522 ⟨32,by decide⟩).lower ∧ (cell12522 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12522 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12522 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12522 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12522 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12522 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12522,cell12522,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12522 ⟨33,by decide⟩).lower ∧ (cell12522 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12522 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12522 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12522 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12522 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12522 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12522,cell12522,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12522 ⟨34,by decide⟩).lower ∧ (cell12522 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12522 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12522 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12522 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12522 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12522 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12522,cell12522,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12522 ⟨35,by decide⟩).lower ∧ (cell12522 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12522 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12522 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12522 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12522 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12522 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12522,cell12522,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12522 ⟨36,by decide⟩).lower ∧ (cell12522 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12522 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12522 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12522 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12522 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12522 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12522,cell12522,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12522 ⟨37,by decide⟩).lower ∧ (cell12522 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12522 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12522 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12522 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12522 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12522 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12522,cell12522,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12522 ⟨38,by decide⟩).lower ∧ (cell12522 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12522 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12522 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12522 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12522 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12522 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12522,cell12522,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12522 ⟨39,by decide⟩).lower ∧ (cell12522 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12522 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12522 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12522 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12522 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12522 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12522,cell12522,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12522 ⟨40,by decide⟩).lower ∧ (cell12522 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12522 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12522 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12522 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12522 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12522 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12522,cell12522,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12522 ⟨41,by decide⟩).lower ∧ (cell12522 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12522 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12522 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12522 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12522 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12522 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12522,cell12522,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12522 ⟨42,by decide⟩).lower ∧ (cell12522 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12522 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12522 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12522 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12522 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12522 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12522,cell12522,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12522 ⟨43,by decide⟩).lower ∧ (cell12522 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12522 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12522 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12522 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12522 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12522 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12522,cell12522,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12522 ⟨44,by decide⟩).lower ∧ (cell12522 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12522 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12522 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12522 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12522 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12522 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12522,cell12522,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12522 ⟨45,by decide⟩).lower ∧ (cell12522 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12522 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12522 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12522 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12522 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12522 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12522,cell12522,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12522 ⟨46,by decide⟩).lower ∧ (cell12522 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12522 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12522 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12522 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12522 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12522 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12522,cell12522,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12522 ⟨47,by decide⟩).lower ∧ (cell12522 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12522 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12522 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12522 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12522 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12522 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12522,cell12522,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12522 ⟨48,by decide⟩).lower ∧ (cell12522 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12522 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12522 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12522 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12522 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12522 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12522,cell12522,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12522 ⟨49,by decide⟩).lower ∧ (cell12522 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12522 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12522 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12522 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12522 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12522 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12522,cell12522,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12522 ⟨50,by decide⟩).lower ∧ (cell12522 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12522 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12522 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12522 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12522 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12522 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12522,cell12522,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12522 ⟨51,by decide⟩).lower ∧ (cell12522 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12522 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12522 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12522 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12522 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12522 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12522,cell12522,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12522 ⟨52,by decide⟩).lower ∧ (cell12522 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12522 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12522 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12522 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12522 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12522 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12522,cell12522,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12522 i).lower ∧
    (cell12522 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12522 i).upper ≤ (0.532 : ℝ) ∧
    (cell12522 i).centre ≤ (0.1 : ℝ) ∧ (cell12522 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12522 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12522 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12522

/-! The local source numeric instances at 12522 have no network premises. -/
namespace BstLean.Part269.N12522
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12522)
open BstLean.Part268 (cell12522)

noncomputable def sourceNumerics12522 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12522 (cell12522 i)
      scalarRow12522.M scalarRow12522.H scalarRow12522.xi := by
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
    energy_allowance := scalarRow12522.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12522]
    centre_nonneg := (scalarRow12522.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D6.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12522])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12522
/-! Actual 12523 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12523
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12523 ≤ (1.036063630354 : ℝ) := by
  have hr : (111.906210730236 : ℝ) ≤ √(12523 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.906210730236 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12523 12523 (11 / 1000) ≤
    (0.008541859070 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12523) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.906210730236 : ℝ) ≤ √(12523 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12523)
  have hdiv : K / √(12523 : ℝ) ≤ K / 111.906210730236 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.906210730236 ≤ (0.008541859070 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12523.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12523 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12523 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12523 := gPlus_lower 12523
end BstLean.Part269.N12523

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12523
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036063630353 : ℝ) ≤ wn 12523 := by
  have hn : √(12523 : ℝ) ≤ 111.906210730237 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12523 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.906210730237 ≤ 2 / √(12523 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000255503691 : ℝ) ≤ rhoBar 12523 BstLean.Part154.csC ∧
    rhoBar 12523 BstLean.Part154.csC ≤ 0.000255504087 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036063630353 : ℝ) / (1.295212 * 12523) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036063630354 : ℝ) / (1.29521 * 12523) := by gcongr
      _ ≤ (0.000255504087 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12523 BstLean.Part154.csC) ≤ 0.001022081631 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12523 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12523 BstLean.Part154.csC) (piBar (rhoBar 12523 BstLean.Part154.csC)) ≤ 0.000195155876 ∧
    cc1 (rhoBar 12523 BstLean.Part154.csC) (piBar (rhoBar 12523 BstLean.Part154.csC)) ≤ 0.000124178953 ∧
    cc2 (rhoBar 12523 BstLean.Part154.csC) ≤ 0.000072086801 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12523 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12523 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12523 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12523 BstLean.Part154.csC * nuR (rhoBar 12523 BstLean.Part154.csC)) ≤ 0.000511024495 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000255504087 : ℝ) * 0.001022081631 := by gcongr
      _ ≤ (0.000511024495 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12523 BstLean.Part154.csC) * nuR (rhoBar 12523 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001022081631 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12523 BstLean.Part154.csC) * rhoBar 12523 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000255504087 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000255504087 / 2 + 0.399 * 0.001022081631 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000195155876 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000511024495 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124178953 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000255504087 / 1.414213562 := by gcongr
      _ ≤ (0.000072086801 : ℝ) := by norm_num

end BstLean.Part269.N12523

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12523
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12523 BstLean.Part154.csC) (piBar (rhoBar 12523 BstLean.Part154.csC)) ≤ 1.64474E-7 := by
  have hr0 : 0 ≤ rhoBar 12523 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12523 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12523 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12523 BstLean.Part154.csC) (piBar (rhoBar 12523 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12523 BstLean.Part154.csC) (piBar (rhoBar 12523 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12523 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000195155876 : ℝ) ^ 2 + 0.000124178953 ^ 2 + 3 * 0.000072086801 ^ 2 +
        2 * 0.797885 * 0.000195155876 * 0.000124178953 + 2 * 0.000195155876 * 0.000072086801 +
        4 * 0.797885 * 0.000124178953 * 0.000072086801 := by gcongr
    _ ≤ (1.64474E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12523 BstLean.Part154.csC Θ ≤ 0.002667758402 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12523 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12523 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12523 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12523 BstLean.Part154.csC) (piBar (rhoBar 12523 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12523 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036063630354 * 1.64474E-7 / (0.000255503691 : ℝ) := by gcongr
    _ ≤ 0.002667758402 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12523 BstLean.Part154.csC Θ ≤ 0.002960754866 + 0.000674100245 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12523 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12523 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12523 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036063630354 : ℝ) * ((2 * Θ * 0.000255504087 +
        (6863 / 10000) * 0.000255504087 * 12523 * 0.001022081631) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002960754866 + 0.000674100245 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12523 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12523 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12523 0.011 Θ ∧ gammaRatio 12523 0.011 Θ ≤ 0.000087835698 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12523 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036063630354 : ℝ) * 0.525 / ((1 - 0.011) * 12523) := by gcongr
      _ ≤ (0.000087835698 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12523 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12523 0.011 Θ) :=
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
    badAllowance 12523 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000774418828 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12523 BstLean.Part154.csC) 1.22 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 2 (rhoBar 12523 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12523 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12523 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12523 0.011 Θ) 1.12 ≤ 3.3895E-8 := by
    have he : (17.2 : ℝ) ≤ gap 1 (gammaRatio 12523 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12523 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12523 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12523 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12523 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036063630354 : ℝ) * 12523 *
        (2.7751E-8 / 1.1045361 + 3.3895E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000774418828 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12523 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003735173694 + 0.003341858647 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12523

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12523
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12523 BstLean.Part154.csC) (piBar (rhoBar 12523 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12523 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12523 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12523 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12523 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12523 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12523 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12523 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12523 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12523 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12523 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12523 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12523 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12523 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12523 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052857953869 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12523) ≤ 0.010671772132 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12523 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036063630354)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010671772132 + 2 * 0.737676 / 12523) := by gcongr
    _ ≤ (0.052857953869 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12523 12 ≤ 0.0015 := by
  exact BstLean.Part269.S6.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12523

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12523
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560495450690 : ℝ) ≤ plow 12523 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12523) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052996249484)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001400573162) : eMP 12523 0.011 xi bn ≤ 0.001205523147 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12523 : ℝ) * (1 - 0.011))) ≤ 0.000596040163 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001400573162 / (12523 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000596040163 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000596040163 : ℝ) + 3.141593 * 0.052996249484 / (12523 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001205523147 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052996249484)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001400573162) : PiBarMP 12523 12 0.011 xi bn ≤ 0.162398349809 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12523 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037424232284 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.289024616086 : ℝ) ≤ √((12523 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.906210730236 : ℝ) ≤ √(12523 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12523) ≤ 0.124500759805 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037424232284 + 0.052996249484 * 1.772454 / (2 * (111.289024616086 : ℝ))) * (1 + 0.001205523147) +
        8 / (12523 * 111.906210730236) + 0.124500759805 := by gcongr
    _ ≤ (0.162398349809 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052996249484)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001400573162) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283067096790) :
    parallelOracle 12523 0.011 xi bn cd ≤ 0.163403537440 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12523 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12523 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560495450690 : ℝ) ≤ plow 12523 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.906210730236 : ℝ) ≤ √(12523 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.283067096790 : ℝ) / (2 * 0.560495450690 * 111.906210730236)) * 0.162398349809 +
        0.283067096790 ^ 2 / (2 * 0.560495450690 * 111.906210730236) := by gcongr
    _ ≤ (0.163403537440 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052996249484) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001400573162)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283067096790) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12523 12523 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560495450690 : ℝ) ≤ plow 12523 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.906210730236 : ℝ) ≤ √(12523 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12523 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12523 Θ 1.22 ≤ 0.011850106365 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.906210730236 := by gcongr <;> linarith
      _ ≤ (0.011850106365 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12523 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12523 12523 0.011 ≤ 0.008541859070 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12523 12523 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12523 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12523 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12523 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12523 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163403537440 + 0.011850106365 + (0.008541859070 : ℝ) *
        (1 + 2 * (0.283067096790 + 0.011850106365) / (0.560495450690 * 111.906210730236))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12523]

end BstLean.Part269.N12523

/-! The original eight local profiles supply actual 12523 moment certificates. -/
namespace BstLean.Part269.N12523
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12523 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12523 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12523 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052996249484 ∧
    0 ≤ bN 12523 BstLean.Part154.csC (groupTheta g) ∧ bN 12523 BstLean.Part154.csC (groupTheta g) ≤ 0.001400573162 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12523 12523 0.011
      (momentAllowance 12523 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12523 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12523 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12523 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12523 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12523 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230209142921 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12523 0.011
      (momentAllowance 12523 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12523 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12523
/-! The actual computed-centre upper energy formula at 12523. -/
namespace BstLean.Part269.N12523
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12523

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12523
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12523)
open BstLean.Part268 (cell12523)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086024495269
  | 2 => 0.086977481550
  | 3 => 0.087930167822
  | 4 => 0.088884326522
  | 5 => 0.089842088926
  | 6 => 0.090805996783
  | 7 => 0.091779058507
  | 8 => 0.092764809916
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12523 12523 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12523 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003740909217 + 0.003348232271 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S6.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12523

/-! Actual upper energy certificates on all 43 source endpoints at 12523. -/
namespace BstLean.Part269.N12523
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12523)
open BstLean.Part268 (cell12523)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12523 (gMinus 12523) (1 - (cell12523 i).lower) ≤ 1 ∧
    energyUpper 12523 (gMinus 12523) (BstLean.Part211.gPlus 12523)
      (finiteEnergy 12523 12523 0.011) (1 - (cell12523 i).lower) ≤
      (cell12523 i).energy := by
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
      have E := BstLean.Part269.S6.uniformEnergy10 (n := 12523) (by norm_num)
        (q := 1 - (cell12523 ⟨10,by decide⟩).lower)
        (by norm_num [cell12523]) (by norm_num [cell12523])
      exact ⟨E.1,E.2.trans (by norm_num [cell12523])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy11 (n := 12523) (by norm_num)
        (q := 1 - (cell12523 ⟨11,by decide⟩).lower)
        (by norm_num [cell12523]) (by norm_num [cell12523])
      exact ⟨E.1,E.2.trans (by norm_num [cell12523])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy12 (n := 12523) (by norm_num)
        (q := 1 - (cell12523 ⟨12,by decide⟩).lower)
        (by norm_num [cell12523]) (by norm_num [cell12523])
      exact ⟨E.1,E.2.trans (by norm_num [cell12523])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy13 (n := 12523) (by norm_num)
        (q := 1 - (cell12523 ⟨13,by decide⟩).lower)
        (by norm_num [cell12523]) (by norm_num [cell12523])
      exact ⟨E.1,E.2.trans (by norm_num [cell12523])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy14 (n := 12523) (by norm_num)
        (q := 1 - (cell12523 ⟨14,by decide⟩).lower)
        (by norm_num [cell12523]) (by norm_num [cell12523])
      exact ⟨E.1,E.2.trans (by norm_num [cell12523])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy15 (n := 12523) (by norm_num)
        (q := 1 - (cell12523 ⟨15,by decide⟩).lower)
        (by norm_num [cell12523]) (by norm_num [cell12523])
      exact ⟨E.1,E.2.trans (by norm_num [cell12523])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy16 (n := 12523) (by norm_num)
        (q := 1 - (cell12523 ⟨16,by decide⟩).lower)
        (by norm_num [cell12523]) (by norm_num [cell12523])
      exact ⟨E.1,E.2.trans (by norm_num [cell12523])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy17 (n := 12523) (by norm_num)
        (q := 1 - (cell12523 ⟨17,by decide⟩).lower)
        (by norm_num [cell12523]) (by norm_num [cell12523])
      exact ⟨E.1,E.2.trans (by norm_num [cell12523])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy18 (n := 12523) (by norm_num)
        (q := 1 - (cell12523 ⟨18,by decide⟩).lower)
        (by norm_num [cell12523]) (by norm_num [cell12523])
      exact ⟨E.1,E.2.trans (by norm_num [cell12523])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy19 (n := 12523) (by norm_num)
        (q := 1 - (cell12523 ⟨19,by decide⟩).lower)
        (by norm_num [cell12523]) (by norm_num [cell12523])
      exact ⟨E.1,E.2.trans (by norm_num [cell12523])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy20 (n := 12523) (by norm_num)
        (q := 1 - (cell12523 ⟨20,by decide⟩).lower)
        (by norm_num [cell12523]) (by norm_num [cell12523])
      exact ⟨E.1,E.2.trans (by norm_num [cell12523])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy21 (n := 12523) (by norm_num)
        (q := 1 - (cell12523 ⟨21,by decide⟩).lower)
        (by norm_num [cell12523]) (by norm_num [cell12523])
      exact ⟨E.1,E.2.trans (by norm_num [cell12523])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy22 (n := 12523) (by norm_num)
        (q := 1 - (cell12523 ⟨22,by decide⟩).lower)
        (by norm_num [cell12523]) (by norm_num [cell12523])
      exact ⟨E.1,E.2.trans (by norm_num [cell12523])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy23 (n := 12523) (by norm_num)
        (q := 1 - (cell12523 ⟨23,by decide⟩).lower)
        (by norm_num [cell12523]) (by norm_num [cell12523])
      exact ⟨E.1,E.2.trans (by norm_num [cell12523])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy24 (n := 12523) (by norm_num)
        (q := 1 - (cell12523 ⟨24,by decide⟩).lower)
        (by norm_num [cell12523]) (by norm_num [cell12523])
      exact ⟨E.1,E.2.trans (by norm_num [cell12523])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy25 (n := 12523) (by norm_num)
        (q := 1 - (cell12523 ⟨25,by decide⟩).lower)
        (by norm_num [cell12523]) (by norm_num [cell12523])
      exact ⟨E.1,E.2.trans (by norm_num [cell12523])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy26 (n := 12523) (by norm_num)
        (q := 1 - (cell12523 ⟨26,by decide⟩).lower)
        (by norm_num [cell12523]) (by norm_num [cell12523])
      exact ⟨E.1,E.2.trans (by norm_num [cell12523])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy27 (n := 12523) (by norm_num)
        (q := 1 - (cell12523 ⟨27,by decide⟩).lower)
        (by norm_num [cell12523]) (by norm_num [cell12523])
      exact ⟨E.1,E.2.trans (by norm_num [cell12523])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy28 (n := 12523) (by norm_num)
        (q := 1 - (cell12523 ⟨28,by decide⟩).lower)
        (by norm_num [cell12523]) (by norm_num [cell12523])
      exact ⟨E.1,E.2.trans (by norm_num [cell12523])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy29 (n := 12523) (by norm_num)
        (q := 1 - (cell12523 ⟨29,by decide⟩).lower)
        (by norm_num [cell12523]) (by norm_num [cell12523])
      exact ⟨E.1,E.2.trans (by norm_num [cell12523])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy30 (n := 12523) (by norm_num)
        (q := 1 - (cell12523 ⟨30,by decide⟩).lower)
        (by norm_num [cell12523]) (by norm_num [cell12523])
      exact ⟨E.1,E.2.trans (by norm_num [cell12523])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy31 (n := 12523) (by norm_num)
        (q := 1 - (cell12523 ⟨31,by decide⟩).lower)
        (by norm_num [cell12523]) (by norm_num [cell12523])
      exact ⟨E.1,E.2.trans (by norm_num [cell12523])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy32 (n := 12523) (by norm_num)
        (q := 1 - (cell12523 ⟨32,by decide⟩).lower)
        (by norm_num [cell12523]) (by norm_num [cell12523])
      exact ⟨E.1,E.2.trans (by norm_num [cell12523])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy33 (n := 12523) (by norm_num)
        (q := 1 - (cell12523 ⟨33,by decide⟩).lower)
        (by norm_num [cell12523]) (by norm_num [cell12523])
      exact ⟨E.1,E.2.trans (by norm_num [cell12523])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy34 (n := 12523) (by norm_num)
        (q := 1 - (cell12523 ⟨34,by decide⟩).lower)
        (by norm_num [cell12523]) (by norm_num [cell12523])
      exact ⟨E.1,E.2.trans (by norm_num [cell12523])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy35 (n := 12523) (by norm_num)
        (q := 1 - (cell12523 ⟨35,by decide⟩).lower)
        (by norm_num [cell12523]) (by norm_num [cell12523])
      exact ⟨E.1,E.2.trans (by norm_num [cell12523])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy36 (n := 12523) (by norm_num)
        (q := 1 - (cell12523 ⟨36,by decide⟩).lower)
        (by norm_num [cell12523]) (by norm_num [cell12523])
      exact ⟨E.1,E.2.trans (by norm_num [cell12523])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy37 (n := 12523) (by norm_num)
        (q := 1 - (cell12523 ⟨37,by decide⟩).lower)
        (by norm_num [cell12523]) (by norm_num [cell12523])
      exact ⟨E.1,E.2.trans (by norm_num [cell12523])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy38 (n := 12523) (by norm_num)
        (q := 1 - (cell12523 ⟨38,by decide⟩).lower)
        (by norm_num [cell12523]) (by norm_num [cell12523])
      exact ⟨E.1,E.2.trans (by norm_num [cell12523])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy39 (n := 12523) (by norm_num)
        (q := 1 - (cell12523 ⟨39,by decide⟩).lower)
        (by norm_num [cell12523]) (by norm_num [cell12523])
      exact ⟨E.1,E.2.trans (by norm_num [cell12523])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy40 (n := 12523) (by norm_num)
        (q := 1 - (cell12523 ⟨40,by decide⟩).lower)
        (by norm_num [cell12523]) (by norm_num [cell12523])
      exact ⟨E.1,E.2.trans (by norm_num [cell12523])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy41 (n := 12523) (by norm_num)
        (q := 1 - (cell12523 ⟨41,by decide⟩).lower)
        (by norm_num [cell12523]) (by norm_num [cell12523])
      exact ⟨E.1,E.2.trans (by norm_num [cell12523])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy42 (n := 12523) (by norm_num)
        (q := 1 - (cell12523 ⟨42,by decide⟩).lower)
        (by norm_num [cell12523]) (by norm_num [cell12523])
      exact ⟨E.1,E.2.trans (by norm_num [cell12523])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy43 (n := 12523) (by norm_num)
        (q := 1 - (cell12523 ⟨43,by decide⟩).lower)
        (by norm_num [cell12523]) (by norm_num [cell12523])
      exact ⟨E.1,E.2.trans (by norm_num [cell12523])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy44 (n := 12523) (by norm_num)
        (q := 1 - (cell12523 ⟨44,by decide⟩).lower)
        (by norm_num [cell12523]) (by norm_num [cell12523])
      exact ⟨E.1,E.2.trans (by norm_num [cell12523])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy45 (n := 12523) (by norm_num)
        (q := 1 - (cell12523 ⟨45,by decide⟩).lower)
        (by norm_num [cell12523]) (by norm_num [cell12523])
      exact ⟨E.1,E.2.trans (by norm_num [cell12523])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy46 (n := 12523) (by norm_num)
        (q := 1 - (cell12523 ⟨46,by decide⟩).lower)
        (by norm_num [cell12523]) (by norm_num [cell12523])
      exact ⟨E.1,E.2.trans (by norm_num [cell12523])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy47 (n := 12523) (by norm_num)
        (q := 1 - (cell12523 ⟨47,by decide⟩).lower)
        (by norm_num [cell12523]) (by norm_num [cell12523])
      exact ⟨E.1,E.2.trans (by norm_num [cell12523])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy48 (n := 12523) (by norm_num)
        (q := 1 - (cell12523 ⟨48,by decide⟩).lower)
        (by norm_num [cell12523]) (by norm_num [cell12523])
      exact ⟨E.1,E.2.trans (by norm_num [cell12523])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy49 (n := 12523) (by norm_num)
        (q := 1 - (cell12523 ⟨49,by decide⟩).lower)
        (by norm_num [cell12523]) (by norm_num [cell12523])
      exact ⟨E.1,E.2.trans (by norm_num [cell12523])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy50 (n := 12523) (by norm_num)
        (q := 1 - (cell12523 ⟨50,by decide⟩).lower)
        (by norm_num [cell12523]) (by norm_num [cell12523])
      exact ⟨E.1,E.2.trans (by norm_num [cell12523])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy51 (n := 12523) (by norm_num)
        (q := 1 - (cell12523 ⟨51,by decide⟩).lower)
        (by norm_num [cell12523]) (by norm_num [cell12523])
      exact ⟨E.1,E.2.trans (by norm_num [cell12523])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy52 (n := 12523) (by norm_num)
        (q := 1 - (cell12523 ⟨52,by decide⟩).lower)
        (by norm_num [cell12523]) (by norm_num [cell12523])
      exact ⟨E.1,E.2.trans (by norm_num [cell12523])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12523

/-! Source-cell containment and simple scalar guards at 12523. -/
namespace BstLean.Part269.N12523
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12523)
open BstLean.Part268 (cell12523)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12523 ⟨10,by decide⟩).lower ∧ (cell12523 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12523 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12523 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12523 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12523 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12523 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12523,cell12523,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12523 ⟨11,by decide⟩).lower ∧ (cell12523 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12523 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12523 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12523 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12523 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12523 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12523,cell12523,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12523 ⟨12,by decide⟩).lower ∧ (cell12523 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12523 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12523 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12523 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12523 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12523 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12523,cell12523,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12523 ⟨13,by decide⟩).lower ∧ (cell12523 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12523 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12523 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12523 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12523 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12523 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12523,cell12523,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12523 ⟨14,by decide⟩).lower ∧ (cell12523 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12523 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12523 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12523 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12523 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12523 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12523,cell12523,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12523 ⟨15,by decide⟩).lower ∧ (cell12523 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12523 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12523 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12523 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12523 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12523 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12523,cell12523,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12523 ⟨16,by decide⟩).lower ∧ (cell12523 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12523 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12523 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12523 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12523 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12523 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12523,cell12523,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12523 ⟨17,by decide⟩).lower ∧ (cell12523 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12523 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12523 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12523 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12523 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12523 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12523,cell12523,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12523 ⟨18,by decide⟩).lower ∧ (cell12523 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12523 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12523 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12523 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12523 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12523 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12523,cell12523,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12523 ⟨19,by decide⟩).lower ∧ (cell12523 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12523 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12523 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12523 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12523 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12523 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12523,cell12523,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12523 ⟨20,by decide⟩).lower ∧ (cell12523 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12523 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12523 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12523 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12523 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12523 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12523,cell12523,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12523 ⟨21,by decide⟩).lower ∧ (cell12523 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12523 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12523 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12523 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12523 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12523 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12523,cell12523,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12523 ⟨22,by decide⟩).lower ∧ (cell12523 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12523 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12523 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12523 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12523 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12523 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12523,cell12523,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12523 ⟨23,by decide⟩).lower ∧ (cell12523 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12523 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12523 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12523 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12523 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12523 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12523,cell12523,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12523 ⟨24,by decide⟩).lower ∧ (cell12523 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12523 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12523 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12523 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12523 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12523 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12523,cell12523,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12523 ⟨25,by decide⟩).lower ∧ (cell12523 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12523 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12523 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12523 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12523 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12523 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12523,cell12523,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12523 ⟨26,by decide⟩).lower ∧ (cell12523 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12523 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12523 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12523 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12523 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12523 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12523,cell12523,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12523 ⟨27,by decide⟩).lower ∧ (cell12523 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12523 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12523 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12523 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12523 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12523 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12523,cell12523,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12523 ⟨28,by decide⟩).lower ∧ (cell12523 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12523 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12523 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12523 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12523 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12523 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12523,cell12523,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12523 ⟨29,by decide⟩).lower ∧ (cell12523 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12523 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12523 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12523 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12523 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12523 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12523,cell12523,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12523 ⟨30,by decide⟩).lower ∧ (cell12523 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12523 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12523 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12523 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12523 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12523 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12523,cell12523,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12523 ⟨31,by decide⟩).lower ∧ (cell12523 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12523 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12523 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12523 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12523 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12523 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12523,cell12523,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12523 ⟨32,by decide⟩).lower ∧ (cell12523 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12523 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12523 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12523 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12523 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12523 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12523,cell12523,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12523 ⟨33,by decide⟩).lower ∧ (cell12523 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12523 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12523 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12523 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12523 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12523 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12523,cell12523,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12523 ⟨34,by decide⟩).lower ∧ (cell12523 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12523 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12523 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12523 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12523 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12523 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12523,cell12523,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12523 ⟨35,by decide⟩).lower ∧ (cell12523 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12523 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12523 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12523 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12523 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12523 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12523,cell12523,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12523 ⟨36,by decide⟩).lower ∧ (cell12523 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12523 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12523 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12523 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12523 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12523 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12523,cell12523,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12523 ⟨37,by decide⟩).lower ∧ (cell12523 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12523 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12523 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12523 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12523 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12523 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12523,cell12523,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12523 ⟨38,by decide⟩).lower ∧ (cell12523 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12523 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12523 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12523 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12523 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12523 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12523,cell12523,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12523 ⟨39,by decide⟩).lower ∧ (cell12523 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12523 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12523 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12523 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12523 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12523 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12523,cell12523,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12523 ⟨40,by decide⟩).lower ∧ (cell12523 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12523 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12523 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12523 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12523 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12523 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12523,cell12523,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12523 ⟨41,by decide⟩).lower ∧ (cell12523 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12523 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12523 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12523 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12523 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12523 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12523,cell12523,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12523 ⟨42,by decide⟩).lower ∧ (cell12523 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12523 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12523 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12523 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12523 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12523 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12523,cell12523,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12523 ⟨43,by decide⟩).lower ∧ (cell12523 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12523 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12523 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12523 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12523 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12523 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12523,cell12523,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12523 ⟨44,by decide⟩).lower ∧ (cell12523 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12523 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12523 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12523 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12523 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12523 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12523,cell12523,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12523 ⟨45,by decide⟩).lower ∧ (cell12523 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12523 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12523 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12523 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12523 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12523 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12523,cell12523,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12523 ⟨46,by decide⟩).lower ∧ (cell12523 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12523 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12523 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12523 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12523 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12523 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12523,cell12523,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12523 ⟨47,by decide⟩).lower ∧ (cell12523 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12523 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12523 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12523 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12523 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12523 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12523,cell12523,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12523 ⟨48,by decide⟩).lower ∧ (cell12523 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12523 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12523 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12523 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12523 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12523 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12523,cell12523,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12523 ⟨49,by decide⟩).lower ∧ (cell12523 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12523 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12523 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12523 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12523 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12523 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12523,cell12523,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12523 ⟨50,by decide⟩).lower ∧ (cell12523 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12523 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12523 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12523 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12523 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12523 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12523,cell12523,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12523 ⟨51,by decide⟩).lower ∧ (cell12523 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12523 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12523 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12523 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12523 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12523 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12523,cell12523,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12523 ⟨52,by decide⟩).lower ∧ (cell12523 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12523 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12523 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12523 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12523 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12523 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12523,cell12523,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12523 i).lower ∧
    (cell12523 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12523 i).upper ≤ (0.532 : ℝ) ∧
    (cell12523 i).centre ≤ (0.1 : ℝ) ∧ (cell12523 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12523 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12523 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12523

/-! The local source numeric instances at 12523 have no network premises. -/
namespace BstLean.Part269.N12523
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12523)
open BstLean.Part268 (cell12523)

noncomputable def sourceNumerics12523 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12523 (cell12523 i)
      scalarRow12523.M scalarRow12523.H scalarRow12523.xi := by
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
    energy_allowance := scalarRow12523.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12523]
    centre_nonneg := (scalarRow12523.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D6.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12523])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12523
/-! Actual 12524 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12524
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12524 ≤ (1.036062177793 : ℝ) := by
  have hr : (111.910678668302 : ℝ) ≤ √(12524 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.910678668302 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12524 12524 (11 / 1000) ≤
    (0.008541518040 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12524) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.910678668302 : ℝ) ≤ √(12524 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12524)
  have hdiv : K / √(12524 : ℝ) ≤ K / 111.910678668302 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.910678668302 ≤ (0.008541518040 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12524.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12524 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12524 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12524 := gPlus_lower 12524
end BstLean.Part269.N12524

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12524
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036062177792 : ℝ) ≤ wn 12524 := by
  have hn : √(12524 : ℝ) ≤ 111.910678668303 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12524 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.910678668303 ≤ 2 / √(12524 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000255482932 : ℝ) ≤ rhoBar 12524 BstLean.Part154.csC ∧
    rhoBar 12524 BstLean.Part154.csC ≤ 0.000255483328 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036062177792 : ℝ) / (1.295212 * 12524) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036062177793 : ℝ) / (1.29521 * 12524) := by gcongr
      _ ≤ (0.000255483328 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12524 BstLean.Part154.csC) ≤ 0.001021998584 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12524 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12524 BstLean.Part154.csC) (piBar (rhoBar 12524 BstLean.Part154.csC)) ≤ 0.000195140019 ∧
    cc1 (rhoBar 12524 BstLean.Part154.csC) (piBar (rhoBar 12524 BstLean.Part154.csC)) ≤ 0.000124168863 ∧
    cc2 (rhoBar 12524 BstLean.Part154.csC) ≤ 0.000072080944 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12524 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12524 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12524 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12524 BstLean.Part154.csC * nuR (rhoBar 12524 BstLean.Part154.csC)) ≤ 0.000510982974 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000255483328 : ℝ) * 0.001021998584 := by gcongr
      _ ≤ (0.000510982974 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12524 BstLean.Part154.csC) * nuR (rhoBar 12524 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001021998584 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12524 BstLean.Part154.csC) * rhoBar 12524 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000255483328 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000255483328 / 2 + 0.399 * 0.001021998584 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000195140019 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000510982974 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124168863 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000255483328 / 1.414213562 := by gcongr
      _ ≤ (0.000072080944 : ℝ) := by norm_num

end BstLean.Part269.N12524

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12524
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12524 BstLean.Part154.csC) (piBar (rhoBar 12524 BstLean.Part154.csC)) ≤ 1.64448E-7 := by
  have hr0 : 0 ≤ rhoBar 12524 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12524 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12524 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12524 BstLean.Part154.csC) (piBar (rhoBar 12524 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12524 BstLean.Part154.csC) (piBar (rhoBar 12524 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12524 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000195140019 : ℝ) ^ 2 + 0.000124168863 ^ 2 + 3 * 0.000072080944 ^ 2 +
        2 * 0.797885 * 0.000195140019 * 0.000124168863 + 2 * 0.000195140019 * 0.000072080944 +
        4 * 0.797885 * 0.000124168863 * 0.000072080944 := by gcongr
    _ ≤ (1.64448E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12524 BstLean.Part154.csC Θ ≤ 0.002667549675 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12524 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12524 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12524 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12524 BstLean.Part154.csC) (piBar (rhoBar 12524 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12524 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036062177793 * 1.64448E-7 / (0.000255482932 : ℝ) := by gcongr
    _ ≤ 0.002667549675 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12524 BstLean.Part154.csC Θ ≤ 0.002960505999 + 0.000674044531 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12524 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12524 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12524 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036062177793 : ℝ) * ((2 * Θ * 0.000255483328 +
        (6863 / 10000) * 0.000255483328 * 12524 * 0.001021998584) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002960505999 + 0.000674044531 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12524 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12524 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12524 0.011 Θ ∧ gammaRatio 12524 0.011 Θ ≤ 0.000087828562 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12524 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036062177793 : ℝ) * 0.525 / ((1 - 0.011) * 12524) := by gcongr
      _ ≤ (0.000087828562 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12524 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12524 0.011 Θ) :=
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
    badAllowance 12524 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000774418828 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12524 BstLean.Part154.csC) 1.22 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 2 (rhoBar 12524 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12524 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12524 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12524 0.011 Θ) 1.12 ≤ 3.3895E-8 := by
    have he : (17.2 : ℝ) ≤ gap 1 (gammaRatio 12524 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12524 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12524 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12524 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12524 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036062177793 : ℝ) * 12524 *
        (2.7751E-8 / 1.1045361 + 3.3895E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000774418828 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12524 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003734924827 + 0.003341594206 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12524

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12524
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12524 BstLean.Part154.csC) (piBar (rhoBar 12524 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12524 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12524 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12524 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12524 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12524 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12524 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12524 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12524 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12524 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12524 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12524 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12524 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12524 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12524 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052855820520 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12524) ≤ 0.010671346071 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12524 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036062177793)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010671346071 + 2 * 0.737676 / 12524) := by gcongr
    _ ≤ (0.052855820520 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12524 12 ≤ 0.0015 := by
  exact BstLean.Part269.S6.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12524

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12524
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560495497197 : ℝ) ≤ plow 12524 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12524) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052995861786)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001400463580) : eMP 12524 0.011 xi bn ≤ 0.001205427747 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12524 : ℝ) * (1 - 0.011))) ≤ 0.000595993049 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001400463580 / (12524 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000595993049 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000595993049 : ℝ) + 3.141593 * 0.052995861786 / (12524 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001205427747 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052995861786)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001400463580) : PiBarMP 12524 12 0.011 xi bn ≤ 0.162391889124 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12524 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037422768204 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.293467912541 : ℝ) ≤ √((12524 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.910678668302 : ℝ) ≤ √(12524 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12524) ≤ 0.124495789219 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037422768204 + 0.052995861786 * 1.772454 / (2 * (111.293467912541 : ℝ))) * (1 + 0.001205427747) +
        8 / (12524 * 111.910678668302) + 0.124495789219 := by gcongr
    _ ≤ (0.162391889124 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052995861786)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001400463580) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283064121383) :
    parallelOracle 12524 0.011 xi bn cd ≤ 0.163397004683 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12524 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12524 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560495497197 : ℝ) ≤ plow 12524 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.910678668302 : ℝ) ≤ √(12524 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.283064121383 : ℝ) / (2 * 0.560495497197 * 111.910678668302)) * 0.162391889124 +
        0.283064121383 ^ 2 / (2 * 0.560495497197 * 111.910678668302) := by gcongr
    _ ≤ (0.163397004683 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052995861786) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001400463580)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283064121383) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12524 12524 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560495497197 : ℝ) ≤ plow 12524 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.910678668302 : ℝ) ≤ √(12524 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12524 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12524 Θ 1.22 ≤ 0.011849633260 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.910678668302 := by gcongr <;> linarith
      _ ≤ (0.011849633260 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12524 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12524 12524 0.011 ≤ 0.008541518040 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12524 12524 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12524 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12524 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12524 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12524 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163397004683 + 0.011849633260 + (0.008541518040 : ℝ) *
        (1 + 2 * (0.283064121383 + 0.011849633260) / (0.560495497197 * 111.910678668302))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12524]

end BstLean.Part269.N12524

/-! The original eight local profiles supply actual 12524 moment certificates. -/
namespace BstLean.Part269.N12524
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12524 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12524 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12524 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052995861786 ∧
    0 ≤ bN 12524 BstLean.Part154.csC (groupTheta g) ∧ bN 12524 BstLean.Part154.csC (groupTheta g) ≤ 0.001400463580 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12524 12524 0.011
      (momentAllowance 12524 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12524 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12524 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12524 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12524 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12524 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230208300863 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12524 0.011
      (momentAllowance 12524 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12524 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12524
/-! The actual computed-centre upper energy formula at 12524. -/
namespace BstLean.Part269.N12524
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12524

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12524
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12524)
open BstLean.Part268 (cell12524)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086021369179
  | 2 => 0.086974293054
  | 3 => 0.087926907033
  | 4 => 0.088880981337
  | 5 => 0.089838644644
  | 6 => 0.090802435682
  | 7 => 0.091775359368
  | 8 => 0.092760947499
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12524 12524 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12524 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003740909217 + 0.003348232271 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S6.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12524

/-! Actual upper energy certificates on all 43 source endpoints at 12524. -/
namespace BstLean.Part269.N12524
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12524)
open BstLean.Part268 (cell12524)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12524 (gMinus 12524) (1 - (cell12524 i).lower) ≤ 1 ∧
    energyUpper 12524 (gMinus 12524) (BstLean.Part211.gPlus 12524)
      (finiteEnergy 12524 12524 0.011) (1 - (cell12524 i).lower) ≤
      (cell12524 i).energy := by
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
      have E := BstLean.Part269.S6.uniformEnergy10 (n := 12524) (by norm_num)
        (q := 1 - (cell12524 ⟨10,by decide⟩).lower)
        (by norm_num [cell12524]) (by norm_num [cell12524])
      exact ⟨E.1,E.2.trans (by norm_num [cell12524])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy11 (n := 12524) (by norm_num)
        (q := 1 - (cell12524 ⟨11,by decide⟩).lower)
        (by norm_num [cell12524]) (by norm_num [cell12524])
      exact ⟨E.1,E.2.trans (by norm_num [cell12524])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy12 (n := 12524) (by norm_num)
        (q := 1 - (cell12524 ⟨12,by decide⟩).lower)
        (by norm_num [cell12524]) (by norm_num [cell12524])
      exact ⟨E.1,E.2.trans (by norm_num [cell12524])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy13 (n := 12524) (by norm_num)
        (q := 1 - (cell12524 ⟨13,by decide⟩).lower)
        (by norm_num [cell12524]) (by norm_num [cell12524])
      exact ⟨E.1,E.2.trans (by norm_num [cell12524])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy14 (n := 12524) (by norm_num)
        (q := 1 - (cell12524 ⟨14,by decide⟩).lower)
        (by norm_num [cell12524]) (by norm_num [cell12524])
      exact ⟨E.1,E.2.trans (by norm_num [cell12524])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy15 (n := 12524) (by norm_num)
        (q := 1 - (cell12524 ⟨15,by decide⟩).lower)
        (by norm_num [cell12524]) (by norm_num [cell12524])
      exact ⟨E.1,E.2.trans (by norm_num [cell12524])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy16 (n := 12524) (by norm_num)
        (q := 1 - (cell12524 ⟨16,by decide⟩).lower)
        (by norm_num [cell12524]) (by norm_num [cell12524])
      exact ⟨E.1,E.2.trans (by norm_num [cell12524])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy17 (n := 12524) (by norm_num)
        (q := 1 - (cell12524 ⟨17,by decide⟩).lower)
        (by norm_num [cell12524]) (by norm_num [cell12524])
      exact ⟨E.1,E.2.trans (by norm_num [cell12524])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy18 (n := 12524) (by norm_num)
        (q := 1 - (cell12524 ⟨18,by decide⟩).lower)
        (by norm_num [cell12524]) (by norm_num [cell12524])
      exact ⟨E.1,E.2.trans (by norm_num [cell12524])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy19 (n := 12524) (by norm_num)
        (q := 1 - (cell12524 ⟨19,by decide⟩).lower)
        (by norm_num [cell12524]) (by norm_num [cell12524])
      exact ⟨E.1,E.2.trans (by norm_num [cell12524])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy20 (n := 12524) (by norm_num)
        (q := 1 - (cell12524 ⟨20,by decide⟩).lower)
        (by norm_num [cell12524]) (by norm_num [cell12524])
      exact ⟨E.1,E.2.trans (by norm_num [cell12524])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy21 (n := 12524) (by norm_num)
        (q := 1 - (cell12524 ⟨21,by decide⟩).lower)
        (by norm_num [cell12524]) (by norm_num [cell12524])
      exact ⟨E.1,E.2.trans (by norm_num [cell12524])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy22 (n := 12524) (by norm_num)
        (q := 1 - (cell12524 ⟨22,by decide⟩).lower)
        (by norm_num [cell12524]) (by norm_num [cell12524])
      exact ⟨E.1,E.2.trans (by norm_num [cell12524])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy23 (n := 12524) (by norm_num)
        (q := 1 - (cell12524 ⟨23,by decide⟩).lower)
        (by norm_num [cell12524]) (by norm_num [cell12524])
      exact ⟨E.1,E.2.trans (by norm_num [cell12524])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy24 (n := 12524) (by norm_num)
        (q := 1 - (cell12524 ⟨24,by decide⟩).lower)
        (by norm_num [cell12524]) (by norm_num [cell12524])
      exact ⟨E.1,E.2.trans (by norm_num [cell12524])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy25 (n := 12524) (by norm_num)
        (q := 1 - (cell12524 ⟨25,by decide⟩).lower)
        (by norm_num [cell12524]) (by norm_num [cell12524])
      exact ⟨E.1,E.2.trans (by norm_num [cell12524])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy26 (n := 12524) (by norm_num)
        (q := 1 - (cell12524 ⟨26,by decide⟩).lower)
        (by norm_num [cell12524]) (by norm_num [cell12524])
      exact ⟨E.1,E.2.trans (by norm_num [cell12524])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy27 (n := 12524) (by norm_num)
        (q := 1 - (cell12524 ⟨27,by decide⟩).lower)
        (by norm_num [cell12524]) (by norm_num [cell12524])
      exact ⟨E.1,E.2.trans (by norm_num [cell12524])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy28 (n := 12524) (by norm_num)
        (q := 1 - (cell12524 ⟨28,by decide⟩).lower)
        (by norm_num [cell12524]) (by norm_num [cell12524])
      exact ⟨E.1,E.2.trans (by norm_num [cell12524])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy29 (n := 12524) (by norm_num)
        (q := 1 - (cell12524 ⟨29,by decide⟩).lower)
        (by norm_num [cell12524]) (by norm_num [cell12524])
      exact ⟨E.1,E.2.trans (by norm_num [cell12524])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy30 (n := 12524) (by norm_num)
        (q := 1 - (cell12524 ⟨30,by decide⟩).lower)
        (by norm_num [cell12524]) (by norm_num [cell12524])
      exact ⟨E.1,E.2.trans (by norm_num [cell12524])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy31 (n := 12524) (by norm_num)
        (q := 1 - (cell12524 ⟨31,by decide⟩).lower)
        (by norm_num [cell12524]) (by norm_num [cell12524])
      exact ⟨E.1,E.2.trans (by norm_num [cell12524])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy32 (n := 12524) (by norm_num)
        (q := 1 - (cell12524 ⟨32,by decide⟩).lower)
        (by norm_num [cell12524]) (by norm_num [cell12524])
      exact ⟨E.1,E.2.trans (by norm_num [cell12524])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy33 (n := 12524) (by norm_num)
        (q := 1 - (cell12524 ⟨33,by decide⟩).lower)
        (by norm_num [cell12524]) (by norm_num [cell12524])
      exact ⟨E.1,E.2.trans (by norm_num [cell12524])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy34 (n := 12524) (by norm_num)
        (q := 1 - (cell12524 ⟨34,by decide⟩).lower)
        (by norm_num [cell12524]) (by norm_num [cell12524])
      exact ⟨E.1,E.2.trans (by norm_num [cell12524])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy35 (n := 12524) (by norm_num)
        (q := 1 - (cell12524 ⟨35,by decide⟩).lower)
        (by norm_num [cell12524]) (by norm_num [cell12524])
      exact ⟨E.1,E.2.trans (by norm_num [cell12524])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy36 (n := 12524) (by norm_num)
        (q := 1 - (cell12524 ⟨36,by decide⟩).lower)
        (by norm_num [cell12524]) (by norm_num [cell12524])
      exact ⟨E.1,E.2.trans (by norm_num [cell12524])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy37 (n := 12524) (by norm_num)
        (q := 1 - (cell12524 ⟨37,by decide⟩).lower)
        (by norm_num [cell12524]) (by norm_num [cell12524])
      exact ⟨E.1,E.2.trans (by norm_num [cell12524])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy38 (n := 12524) (by norm_num)
        (q := 1 - (cell12524 ⟨38,by decide⟩).lower)
        (by norm_num [cell12524]) (by norm_num [cell12524])
      exact ⟨E.1,E.2.trans (by norm_num [cell12524])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy39 (n := 12524) (by norm_num)
        (q := 1 - (cell12524 ⟨39,by decide⟩).lower)
        (by norm_num [cell12524]) (by norm_num [cell12524])
      exact ⟨E.1,E.2.trans (by norm_num [cell12524])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy40 (n := 12524) (by norm_num)
        (q := 1 - (cell12524 ⟨40,by decide⟩).lower)
        (by norm_num [cell12524]) (by norm_num [cell12524])
      exact ⟨E.1,E.2.trans (by norm_num [cell12524])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy41 (n := 12524) (by norm_num)
        (q := 1 - (cell12524 ⟨41,by decide⟩).lower)
        (by norm_num [cell12524]) (by norm_num [cell12524])
      exact ⟨E.1,E.2.trans (by norm_num [cell12524])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy42 (n := 12524) (by norm_num)
        (q := 1 - (cell12524 ⟨42,by decide⟩).lower)
        (by norm_num [cell12524]) (by norm_num [cell12524])
      exact ⟨E.1,E.2.trans (by norm_num [cell12524])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy43 (n := 12524) (by norm_num)
        (q := 1 - (cell12524 ⟨43,by decide⟩).lower)
        (by norm_num [cell12524]) (by norm_num [cell12524])
      exact ⟨E.1,E.2.trans (by norm_num [cell12524])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy44 (n := 12524) (by norm_num)
        (q := 1 - (cell12524 ⟨44,by decide⟩).lower)
        (by norm_num [cell12524]) (by norm_num [cell12524])
      exact ⟨E.1,E.2.trans (by norm_num [cell12524])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy45 (n := 12524) (by norm_num)
        (q := 1 - (cell12524 ⟨45,by decide⟩).lower)
        (by norm_num [cell12524]) (by norm_num [cell12524])
      exact ⟨E.1,E.2.trans (by norm_num [cell12524])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy46 (n := 12524) (by norm_num)
        (q := 1 - (cell12524 ⟨46,by decide⟩).lower)
        (by norm_num [cell12524]) (by norm_num [cell12524])
      exact ⟨E.1,E.2.trans (by norm_num [cell12524])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy47 (n := 12524) (by norm_num)
        (q := 1 - (cell12524 ⟨47,by decide⟩).lower)
        (by norm_num [cell12524]) (by norm_num [cell12524])
      exact ⟨E.1,E.2.trans (by norm_num [cell12524])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy48 (n := 12524) (by norm_num)
        (q := 1 - (cell12524 ⟨48,by decide⟩).lower)
        (by norm_num [cell12524]) (by norm_num [cell12524])
      exact ⟨E.1,E.2.trans (by norm_num [cell12524])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy49 (n := 12524) (by norm_num)
        (q := 1 - (cell12524 ⟨49,by decide⟩).lower)
        (by norm_num [cell12524]) (by norm_num [cell12524])
      exact ⟨E.1,E.2.trans (by norm_num [cell12524])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy50 (n := 12524) (by norm_num)
        (q := 1 - (cell12524 ⟨50,by decide⟩).lower)
        (by norm_num [cell12524]) (by norm_num [cell12524])
      exact ⟨E.1,E.2.trans (by norm_num [cell12524])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy51 (n := 12524) (by norm_num)
        (q := 1 - (cell12524 ⟨51,by decide⟩).lower)
        (by norm_num [cell12524]) (by norm_num [cell12524])
      exact ⟨E.1,E.2.trans (by norm_num [cell12524])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy52 (n := 12524) (by norm_num)
        (q := 1 - (cell12524 ⟨52,by decide⟩).lower)
        (by norm_num [cell12524]) (by norm_num [cell12524])
      exact ⟨E.1,E.2.trans (by norm_num [cell12524])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12524

/-! Source-cell containment and simple scalar guards at 12524. -/
namespace BstLean.Part269.N12524
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12524)
open BstLean.Part268 (cell12524)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12524 ⟨10,by decide⟩).lower ∧ (cell12524 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12524 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12524 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12524 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12524 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12524 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12524,cell12524,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12524 ⟨11,by decide⟩).lower ∧ (cell12524 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12524 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12524 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12524 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12524 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12524 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12524,cell12524,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12524 ⟨12,by decide⟩).lower ∧ (cell12524 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12524 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12524 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12524 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12524 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12524 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12524,cell12524,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12524 ⟨13,by decide⟩).lower ∧ (cell12524 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12524 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12524 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12524 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12524 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12524 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12524,cell12524,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12524 ⟨14,by decide⟩).lower ∧ (cell12524 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12524 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12524 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12524 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12524 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12524 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12524,cell12524,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12524 ⟨15,by decide⟩).lower ∧ (cell12524 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12524 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12524 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12524 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12524 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12524 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12524,cell12524,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12524 ⟨16,by decide⟩).lower ∧ (cell12524 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12524 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12524 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12524 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12524 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12524 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12524,cell12524,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12524 ⟨17,by decide⟩).lower ∧ (cell12524 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12524 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12524 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12524 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12524 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12524 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12524,cell12524,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12524 ⟨18,by decide⟩).lower ∧ (cell12524 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12524 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12524 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12524 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12524 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12524 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12524,cell12524,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12524 ⟨19,by decide⟩).lower ∧ (cell12524 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12524 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12524 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12524 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12524 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12524 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12524,cell12524,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12524 ⟨20,by decide⟩).lower ∧ (cell12524 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12524 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12524 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12524 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12524 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12524 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12524,cell12524,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12524 ⟨21,by decide⟩).lower ∧ (cell12524 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12524 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12524 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12524 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12524 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12524 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12524,cell12524,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12524 ⟨22,by decide⟩).lower ∧ (cell12524 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12524 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12524 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12524 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12524 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12524 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12524,cell12524,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12524 ⟨23,by decide⟩).lower ∧ (cell12524 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12524 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12524 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12524 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12524 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12524 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12524,cell12524,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12524 ⟨24,by decide⟩).lower ∧ (cell12524 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12524 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12524 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12524 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12524 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12524 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12524,cell12524,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12524 ⟨25,by decide⟩).lower ∧ (cell12524 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12524 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12524 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12524 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12524 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12524 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12524,cell12524,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12524 ⟨26,by decide⟩).lower ∧ (cell12524 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12524 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12524 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12524 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12524 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12524 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12524,cell12524,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12524 ⟨27,by decide⟩).lower ∧ (cell12524 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12524 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12524 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12524 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12524 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12524 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12524,cell12524,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12524 ⟨28,by decide⟩).lower ∧ (cell12524 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12524 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12524 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12524 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12524 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12524 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12524,cell12524,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12524 ⟨29,by decide⟩).lower ∧ (cell12524 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12524 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12524 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12524 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12524 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12524 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12524,cell12524,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12524 ⟨30,by decide⟩).lower ∧ (cell12524 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12524 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12524 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12524 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12524 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12524 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12524,cell12524,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12524 ⟨31,by decide⟩).lower ∧ (cell12524 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12524 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12524 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12524 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12524 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12524 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12524,cell12524,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12524 ⟨32,by decide⟩).lower ∧ (cell12524 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12524 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12524 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12524 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12524 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12524 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12524,cell12524,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12524 ⟨33,by decide⟩).lower ∧ (cell12524 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12524 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12524 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12524 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12524 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12524 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12524,cell12524,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12524 ⟨34,by decide⟩).lower ∧ (cell12524 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12524 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12524 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12524 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12524 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12524 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12524,cell12524,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12524 ⟨35,by decide⟩).lower ∧ (cell12524 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12524 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12524 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12524 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12524 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12524 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12524,cell12524,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12524 ⟨36,by decide⟩).lower ∧ (cell12524 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12524 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12524 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12524 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12524 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12524 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12524,cell12524,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12524 ⟨37,by decide⟩).lower ∧ (cell12524 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12524 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12524 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12524 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12524 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12524 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12524,cell12524,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12524 ⟨38,by decide⟩).lower ∧ (cell12524 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12524 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12524 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12524 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12524 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12524 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12524,cell12524,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12524 ⟨39,by decide⟩).lower ∧ (cell12524 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12524 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12524 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12524 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12524 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12524 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12524,cell12524,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12524 ⟨40,by decide⟩).lower ∧ (cell12524 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12524 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12524 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12524 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12524 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12524 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12524,cell12524,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12524 ⟨41,by decide⟩).lower ∧ (cell12524 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12524 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12524 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12524 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12524 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12524 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12524,cell12524,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12524 ⟨42,by decide⟩).lower ∧ (cell12524 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12524 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12524 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12524 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12524 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12524 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12524,cell12524,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12524 ⟨43,by decide⟩).lower ∧ (cell12524 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12524 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12524 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12524 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12524 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12524 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12524,cell12524,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12524 ⟨44,by decide⟩).lower ∧ (cell12524 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12524 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12524 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12524 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12524 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12524 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12524,cell12524,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12524 ⟨45,by decide⟩).lower ∧ (cell12524 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12524 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12524 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12524 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12524 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12524 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12524,cell12524,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12524 ⟨46,by decide⟩).lower ∧ (cell12524 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12524 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12524 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12524 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12524 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12524 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12524,cell12524,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12524 ⟨47,by decide⟩).lower ∧ (cell12524 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12524 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12524 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12524 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12524 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12524 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12524,cell12524,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12524 ⟨48,by decide⟩).lower ∧ (cell12524 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12524 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12524 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12524 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12524 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12524 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12524,cell12524,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12524 ⟨49,by decide⟩).lower ∧ (cell12524 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12524 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12524 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12524 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12524 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12524 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12524,cell12524,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12524 ⟨50,by decide⟩).lower ∧ (cell12524 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12524 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12524 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12524 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12524 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12524 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12524,cell12524,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12524 ⟨51,by decide⟩).lower ∧ (cell12524 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12524 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12524 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12524 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12524 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12524 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12524,cell12524,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12524 ⟨52,by decide⟩).lower ∧ (cell12524 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12524 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12524 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12524 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12524 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12524 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12524,cell12524,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12524 i).lower ∧
    (cell12524 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12524 i).upper ≤ (0.532 : ℝ) ∧
    (cell12524 i).centre ≤ (0.1 : ℝ) ∧ (cell12524 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12524 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12524 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12524

/-! The local source numeric instances at 12524 have no network premises. -/
namespace BstLean.Part269.N12524
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12524)
open BstLean.Part268 (cell12524)

noncomputable def sourceNumerics12524 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12524 (cell12524 i)
      scalarRow12524.M scalarRow12524.H scalarRow12524.xi := by
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
    energy_allowance := scalarRow12524.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12524]
    centre_nonneg := (scalarRow12524.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D6.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12524])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12524