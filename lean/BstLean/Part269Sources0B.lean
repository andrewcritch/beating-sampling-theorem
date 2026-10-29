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
/-! Actual 12364 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12364
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12364 ≤ (1.036296837591 : ℝ) := by
  have hr : (111.193524991341 : ℝ) ≤ √(12364 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.193524991341 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12364 12364 (11 / 1000) ≤
    (0.008596607843 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12364) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.193524991341 : ℝ) ≤ √(12364 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12364)
  have hdiv : K / √(12364 : ℝ) ≤ K / 111.193524991341 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.193524991341 ≤ (0.008596607843 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12364.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12364 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12364 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12364 := gPlus_lower 12364
end BstLean.Part269.N12364

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12364
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036296837590 : ℝ) ≤ wn 12364 := by
  have hn : √(12364 : ℝ) ≤ 111.193524991342 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12364 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.193524991342 ≤ 2 / √(12364 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000258847698 : ℝ) ≤ rhoBar 12364 BstLean.Part154.csC ∧
    rhoBar 12364 BstLean.Part154.csC ≤ 0.000258848099 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036296837590 : ℝ) / (1.295212 * 12364) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036296837591 : ℝ) / (1.29521 * 12364) := by gcongr
      _ ≤ (0.000258848099 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12364 BstLean.Part154.csC) ≤ 0.001035459399 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12364 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12364 BstLean.Part154.csC) (piBar (rhoBar 12364 BstLean.Part154.csC)) ≤ 0.000197710179 ∧
    cc1 (rhoBar 12364 BstLean.Part154.csC) (piBar (rhoBar 12364 BstLean.Part154.csC)) ≤ 0.000125804247 ∧
    cc2 (rhoBar 12364 BstLean.Part154.csC) ≤ 0.000073030266 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12364 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12364 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12364 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12364 BstLean.Part154.csC * nuR (rhoBar 12364 BstLean.Part154.csC)) ≤ 0.000517712949 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000258848099 : ℝ) * 0.001035459399 := by gcongr
      _ ≤ (0.000517712949 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12364 BstLean.Part154.csC) * nuR (rhoBar 12364 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001035459399 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12364 BstLean.Part154.csC) * rhoBar 12364 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000258848099 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000258848099 / 2 + 0.399 * 0.001035459399 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000197710179 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000517712949 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125804247 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000258848099 / 1.414213562 := by gcongr
      _ ≤ (0.000073030266 : ℝ) := by norm_num

end BstLean.Part269.N12364

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12364
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12364 BstLean.Part154.csC) (piBar (rhoBar 12364 BstLean.Part154.csC)) ≤ 1.68808E-7 := by
  have hr0 : 0 ≤ rhoBar 12364 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12364 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12364 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12364 BstLean.Part154.csC) (piBar (rhoBar 12364 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12364 BstLean.Part154.csC) (piBar (rhoBar 12364 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12364 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000197710179 : ℝ) ^ 2 + 0.000125804247 ^ 2 + 3 * 0.000073030266 ^ 2 +
        2 * 0.797885 * 0.000197710179 * 0.000125804247 + 2 * 0.000197710179 * 0.000073030266 +
        4 * 0.797885 * 0.000125804247 * 0.000073030266 := by gcongr
    _ ≤ (1.68808E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12364 BstLean.Part154.csC Θ ≤ 0.002703291518 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12364 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12364 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12364 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12364 BstLean.Part154.csC) (piBar (rhoBar 12364 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12364 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036296837591 * 1.68808E-7 / (0.000258847698 : ℝ) := by gcongr
    _ ≤ 0.002703291518 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12364 BstLean.Part154.csC Θ ≤ 0.003000857906 + 0.000683076521 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12364 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12364 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12364 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036296837591 : ℝ) * ((2 * Θ * 0.000258848099 +
        (6863 / 10000) * 0.000258848099 * 12364 * 0.001035459399) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003000857906 + 0.000683076521 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12364 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12364 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12364 0.011 Θ ∧ gammaRatio 12364 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12364 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036296837591 : ℝ) * 0.525 / ((1 - 0.011) * 12364) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12364 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12364 0.011 Θ) :=
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
    badAllowance 12364 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12364 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12364 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12364 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12364 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12364 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12364 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12364 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12364 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12364 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12364 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036296837591 : ℝ) * 12364 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12364 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004100857906 + 0.003386368039 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12364

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12364
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12364 BstLean.Part154.csC) (piBar (rhoBar 12364 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12364 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12364 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12364 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12364 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12364 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12364 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12364 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12364 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12364 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12364 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12364 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12364 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12364 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12364 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053200465514 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12364) ≤ 0.010740171977 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12364 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036296837591)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010740171977 + 2 * 0.737676 / 12364) := by gcongr
    _ ≤ (0.053200465514 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12364 12 ≤ 0.0015 := by
  exact BstLean.Part269.S0.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12364

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12364
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560487960441 : ℝ) ≤ plow 12364 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12364) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053385301127)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001419228047) : eMP 12364 0.011 xi bn ≤ 0.001221399904 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12364 : ℝ) * (1 - 0.011))) ≤ 0.000603842128 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001419228047 / (12364 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000603842128 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000603842128 : ℝ) + 3.141593 * 0.053385301127 / (12364 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001221399904 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053385301127)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001419228047) : PiBarMP 12364 12 0.011 xi bn ≤ 0.163451582896 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12364 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037672643218 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.580269487824 : ℝ) ≤ √((12364 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.193524991341 : ℝ) ≤ √(12364 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12364) ≤ 0.125298737169 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037672643218 + 0.053385301127 * 1.772454 / (2 * (110.580269487824 : ℝ))) * (1 + 0.001221399904) +
        8 / (12364 * 111.193524991341) + 0.125298737169 := by gcongr
    _ ≤ (0.163451582896 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053385301127)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001419228047) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284253059369) :
    parallelOracle 12364 0.011 xi bn cd ≤ 0.164472571662 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12364 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12364 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560487960441 : ℝ) ≤ plow 12364 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.193524991341 : ℝ) ≤ √(12364 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284253059369 : ℝ) / (2 * 0.560487960441 * 111.193524991341)) * 0.163451582896 +
        0.284253059369 ^ 2 / (2 * 0.560487960441 * 111.193524991341) := by gcongr
    _ ≤ (0.164472571662 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053385301127) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001419228047)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284253059369) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12364 12364 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560487960441 : ℝ) ≤ plow 12364 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.193524991341 : ℝ) ≤ √(12364 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12364 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12364 Θ 1.22 ≤ 0.011926058646 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.193524991341 := by gcongr <;> linarith
      _ ≤ (0.011926058646 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12364 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12364 12364 0.011 ≤ 0.008596607843 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12364 12364 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12364 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12364 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12364 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12364 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164472571662 + 0.011926058646 + (0.008596607843 : ℝ) *
        (1 + 2 * (0.284253059369 + 0.011926058646) / (0.560487960441 * 111.193524991341))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12364]

end BstLean.Part269.N12364

/-! The original eight local profiles supply actual 12364 moment certificates. -/
namespace BstLean.Part269.N12364
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12364 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12364 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12364 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053385301127 ∧
    0 ≤ bN 12364 BstLean.Part154.csC (groupTheta g) ∧ bN 12364 BstLean.Part154.csC (groupTheta g) ≤ 0.001419228047 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12364 12364 0.011
      (momentAllowance 12364 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12364 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12364 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12364 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12364 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12364 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231052593855 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12364 0.011
      (momentAllowance 12364 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12364 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12364
/-! The actual computed-centre upper energy formula at 12364. -/
namespace BstLean.Part269.N12364
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12364

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12364
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12364)
open BstLean.Part268 (cell12364)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086539084155
  | 2 => 0.087502757717
  | 3 => 0.088467881818
  | 4 => 0.089436616462
  | 5 => 0.090411546172
  | 6 => 0.091395739280
  | 7 => 0.092392812110
  | 8 => 0.093406998006
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12364 12364 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12364 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12364

/-! Actual upper energy certificates on all 43 source endpoints at 12364. -/
namespace BstLean.Part269.N12364
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12364)
open BstLean.Part268 (cell12364)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12364 (gMinus 12364) (1 - (cell12364 i).lower) ≤ 1 ∧
    energyUpper 12364 (gMinus 12364) (BstLean.Part211.gPlus 12364)
      (finiteEnergy 12364 12364 0.011) (1 - (cell12364 i).lower) ≤
      (cell12364 i).energy := by
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
      have E := BstLean.Part269.S0.uniformEnergy10 (n := 12364) (by norm_num)
        (q := 1 - (cell12364 ⟨10,by decide⟩).lower)
        (by norm_num [cell12364]) (by norm_num [cell12364])
      exact ⟨E.1,E.2.trans (by norm_num [cell12364])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy11 (n := 12364) (by norm_num)
        (q := 1 - (cell12364 ⟨11,by decide⟩).lower)
        (by norm_num [cell12364]) (by norm_num [cell12364])
      exact ⟨E.1,E.2.trans (by norm_num [cell12364])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy12 (n := 12364) (by norm_num)
        (q := 1 - (cell12364 ⟨12,by decide⟩).lower)
        (by norm_num [cell12364]) (by norm_num [cell12364])
      exact ⟨E.1,E.2.trans (by norm_num [cell12364])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy13 (n := 12364) (by norm_num)
        (q := 1 - (cell12364 ⟨13,by decide⟩).lower)
        (by norm_num [cell12364]) (by norm_num [cell12364])
      exact ⟨E.1,E.2.trans (by norm_num [cell12364])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy14 (n := 12364) (by norm_num)
        (q := 1 - (cell12364 ⟨14,by decide⟩).lower)
        (by norm_num [cell12364]) (by norm_num [cell12364])
      exact ⟨E.1,E.2.trans (by norm_num [cell12364])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy15 (n := 12364) (by norm_num)
        (q := 1 - (cell12364 ⟨15,by decide⟩).lower)
        (by norm_num [cell12364]) (by norm_num [cell12364])
      exact ⟨E.1,E.2.trans (by norm_num [cell12364])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy16 (n := 12364) (by norm_num)
        (q := 1 - (cell12364 ⟨16,by decide⟩).lower)
        (by norm_num [cell12364]) (by norm_num [cell12364])
      exact ⟨E.1,E.2.trans (by norm_num [cell12364])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy17 (n := 12364) (by norm_num)
        (q := 1 - (cell12364 ⟨17,by decide⟩).lower)
        (by norm_num [cell12364]) (by norm_num [cell12364])
      exact ⟨E.1,E.2.trans (by norm_num [cell12364])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy18 (n := 12364) (by norm_num)
        (q := 1 - (cell12364 ⟨18,by decide⟩).lower)
        (by norm_num [cell12364]) (by norm_num [cell12364])
      exact ⟨E.1,E.2.trans (by norm_num [cell12364])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy19 (n := 12364) (by norm_num)
        (q := 1 - (cell12364 ⟨19,by decide⟩).lower)
        (by norm_num [cell12364]) (by norm_num [cell12364])
      exact ⟨E.1,E.2.trans (by norm_num [cell12364])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy20 (n := 12364) (by norm_num)
        (q := 1 - (cell12364 ⟨20,by decide⟩).lower)
        (by norm_num [cell12364]) (by norm_num [cell12364])
      exact ⟨E.1,E.2.trans (by norm_num [cell12364])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy21 (n := 12364) (by norm_num)
        (q := 1 - (cell12364 ⟨21,by decide⟩).lower)
        (by norm_num [cell12364]) (by norm_num [cell12364])
      exact ⟨E.1,E.2.trans (by norm_num [cell12364])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy22 (n := 12364) (by norm_num)
        (q := 1 - (cell12364 ⟨22,by decide⟩).lower)
        (by norm_num [cell12364]) (by norm_num [cell12364])
      exact ⟨E.1,E.2.trans (by norm_num [cell12364])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy23 (n := 12364) (by norm_num)
        (q := 1 - (cell12364 ⟨23,by decide⟩).lower)
        (by norm_num [cell12364]) (by norm_num [cell12364])
      exact ⟨E.1,E.2.trans (by norm_num [cell12364])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy24 (n := 12364) (by norm_num)
        (q := 1 - (cell12364 ⟨24,by decide⟩).lower)
        (by norm_num [cell12364]) (by norm_num [cell12364])
      exact ⟨E.1,E.2.trans (by norm_num [cell12364])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy25 (n := 12364) (by norm_num)
        (q := 1 - (cell12364 ⟨25,by decide⟩).lower)
        (by norm_num [cell12364]) (by norm_num [cell12364])
      exact ⟨E.1,E.2.trans (by norm_num [cell12364])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy26 (n := 12364) (by norm_num)
        (q := 1 - (cell12364 ⟨26,by decide⟩).lower)
        (by norm_num [cell12364]) (by norm_num [cell12364])
      exact ⟨E.1,E.2.trans (by norm_num [cell12364])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy27 (n := 12364) (by norm_num)
        (q := 1 - (cell12364 ⟨27,by decide⟩).lower)
        (by norm_num [cell12364]) (by norm_num [cell12364])
      exact ⟨E.1,E.2.trans (by norm_num [cell12364])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy28 (n := 12364) (by norm_num)
        (q := 1 - (cell12364 ⟨28,by decide⟩).lower)
        (by norm_num [cell12364]) (by norm_num [cell12364])
      exact ⟨E.1,E.2.trans (by norm_num [cell12364])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy29 (n := 12364) (by norm_num)
        (q := 1 - (cell12364 ⟨29,by decide⟩).lower)
        (by norm_num [cell12364]) (by norm_num [cell12364])
      exact ⟨E.1,E.2.trans (by norm_num [cell12364])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy30 (n := 12364) (by norm_num)
        (q := 1 - (cell12364 ⟨30,by decide⟩).lower)
        (by norm_num [cell12364]) (by norm_num [cell12364])
      exact ⟨E.1,E.2.trans (by norm_num [cell12364])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy31 (n := 12364) (by norm_num)
        (q := 1 - (cell12364 ⟨31,by decide⟩).lower)
        (by norm_num [cell12364]) (by norm_num [cell12364])
      exact ⟨E.1,E.2.trans (by norm_num [cell12364])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy32 (n := 12364) (by norm_num)
        (q := 1 - (cell12364 ⟨32,by decide⟩).lower)
        (by norm_num [cell12364]) (by norm_num [cell12364])
      exact ⟨E.1,E.2.trans (by norm_num [cell12364])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy33 (n := 12364) (by norm_num)
        (q := 1 - (cell12364 ⟨33,by decide⟩).lower)
        (by norm_num [cell12364]) (by norm_num [cell12364])
      exact ⟨E.1,E.2.trans (by norm_num [cell12364])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy34 (n := 12364) (by norm_num)
        (q := 1 - (cell12364 ⟨34,by decide⟩).lower)
        (by norm_num [cell12364]) (by norm_num [cell12364])
      exact ⟨E.1,E.2.trans (by norm_num [cell12364])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy35 (n := 12364) (by norm_num)
        (q := 1 - (cell12364 ⟨35,by decide⟩).lower)
        (by norm_num [cell12364]) (by norm_num [cell12364])
      exact ⟨E.1,E.2.trans (by norm_num [cell12364])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy36 (n := 12364) (by norm_num)
        (q := 1 - (cell12364 ⟨36,by decide⟩).lower)
        (by norm_num [cell12364]) (by norm_num [cell12364])
      exact ⟨E.1,E.2.trans (by norm_num [cell12364])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy37 (n := 12364) (by norm_num)
        (q := 1 - (cell12364 ⟨37,by decide⟩).lower)
        (by norm_num [cell12364]) (by norm_num [cell12364])
      exact ⟨E.1,E.2.trans (by norm_num [cell12364])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy38 (n := 12364) (by norm_num)
        (q := 1 - (cell12364 ⟨38,by decide⟩).lower)
        (by norm_num [cell12364]) (by norm_num [cell12364])
      exact ⟨E.1,E.2.trans (by norm_num [cell12364])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy39 (n := 12364) (by norm_num)
        (q := 1 - (cell12364 ⟨39,by decide⟩).lower)
        (by norm_num [cell12364]) (by norm_num [cell12364])
      exact ⟨E.1,E.2.trans (by norm_num [cell12364])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy40 (n := 12364) (by norm_num)
        (q := 1 - (cell12364 ⟨40,by decide⟩).lower)
        (by norm_num [cell12364]) (by norm_num [cell12364])
      exact ⟨E.1,E.2.trans (by norm_num [cell12364])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy41 (n := 12364) (by norm_num)
        (q := 1 - (cell12364 ⟨41,by decide⟩).lower)
        (by norm_num [cell12364]) (by norm_num [cell12364])
      exact ⟨E.1,E.2.trans (by norm_num [cell12364])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy42 (n := 12364) (by norm_num)
        (q := 1 - (cell12364 ⟨42,by decide⟩).lower)
        (by norm_num [cell12364]) (by norm_num [cell12364])
      exact ⟨E.1,E.2.trans (by norm_num [cell12364])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy43 (n := 12364) (by norm_num)
        (q := 1 - (cell12364 ⟨43,by decide⟩).lower)
        (by norm_num [cell12364]) (by norm_num [cell12364])
      exact ⟨E.1,E.2.trans (by norm_num [cell12364])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy44 (n := 12364) (by norm_num)
        (q := 1 - (cell12364 ⟨44,by decide⟩).lower)
        (by norm_num [cell12364]) (by norm_num [cell12364])
      exact ⟨E.1,E.2.trans (by norm_num [cell12364])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy45 (n := 12364) (by norm_num)
        (q := 1 - (cell12364 ⟨45,by decide⟩).lower)
        (by norm_num [cell12364]) (by norm_num [cell12364])
      exact ⟨E.1,E.2.trans (by norm_num [cell12364])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy46 (n := 12364) (by norm_num)
        (q := 1 - (cell12364 ⟨46,by decide⟩).lower)
        (by norm_num [cell12364]) (by norm_num [cell12364])
      exact ⟨E.1,E.2.trans (by norm_num [cell12364])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy47 (n := 12364) (by norm_num)
        (q := 1 - (cell12364 ⟨47,by decide⟩).lower)
        (by norm_num [cell12364]) (by norm_num [cell12364])
      exact ⟨E.1,E.2.trans (by norm_num [cell12364])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy48 (n := 12364) (by norm_num)
        (q := 1 - (cell12364 ⟨48,by decide⟩).lower)
        (by norm_num [cell12364]) (by norm_num [cell12364])
      exact ⟨E.1,E.2.trans (by norm_num [cell12364])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy49 (n := 12364) (by norm_num)
        (q := 1 - (cell12364 ⟨49,by decide⟩).lower)
        (by norm_num [cell12364]) (by norm_num [cell12364])
      exact ⟨E.1,E.2.trans (by norm_num [cell12364])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy50 (n := 12364) (by norm_num)
        (q := 1 - (cell12364 ⟨50,by decide⟩).lower)
        (by norm_num [cell12364]) (by norm_num [cell12364])
      exact ⟨E.1,E.2.trans (by norm_num [cell12364])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy51 (n := 12364) (by norm_num)
        (q := 1 - (cell12364 ⟨51,by decide⟩).lower)
        (by norm_num [cell12364]) (by norm_num [cell12364])
      exact ⟨E.1,E.2.trans (by norm_num [cell12364])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy52 (n := 12364) (by norm_num)
        (q := 1 - (cell12364 ⟨52,by decide⟩).lower)
        (by norm_num [cell12364]) (by norm_num [cell12364])
      exact ⟨E.1,E.2.trans (by norm_num [cell12364])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12364

/-! Source-cell containment and simple scalar guards at 12364. -/
namespace BstLean.Part269.N12364
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12364)
open BstLean.Part268 (cell12364)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12364 ⟨10,by decide⟩).lower ∧ (cell12364 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12364 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12364 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12364 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12364 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12364 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12364,cell12364,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12364 ⟨11,by decide⟩).lower ∧ (cell12364 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12364 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12364 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12364 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12364 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12364 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12364,cell12364,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12364 ⟨12,by decide⟩).lower ∧ (cell12364 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12364 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12364 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12364 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12364 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12364 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12364,cell12364,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12364 ⟨13,by decide⟩).lower ∧ (cell12364 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12364 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12364 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12364 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12364 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12364 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12364,cell12364,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12364 ⟨14,by decide⟩).lower ∧ (cell12364 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12364 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12364 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12364 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12364 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12364 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12364,cell12364,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12364 ⟨15,by decide⟩).lower ∧ (cell12364 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12364 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12364 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12364 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12364 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12364 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12364,cell12364,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12364 ⟨16,by decide⟩).lower ∧ (cell12364 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12364 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12364 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12364 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12364 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12364 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12364,cell12364,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12364 ⟨17,by decide⟩).lower ∧ (cell12364 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12364 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12364 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12364 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12364 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12364 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12364,cell12364,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12364 ⟨18,by decide⟩).lower ∧ (cell12364 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12364 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12364 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12364 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12364 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12364 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12364,cell12364,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12364 ⟨19,by decide⟩).lower ∧ (cell12364 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12364 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12364 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12364 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12364 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12364 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12364,cell12364,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12364 ⟨20,by decide⟩).lower ∧ (cell12364 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12364 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12364 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12364 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12364 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12364 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12364,cell12364,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12364 ⟨21,by decide⟩).lower ∧ (cell12364 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12364 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12364 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12364 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12364 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12364 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12364,cell12364,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12364 ⟨22,by decide⟩).lower ∧ (cell12364 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12364 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12364 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12364 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12364 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12364 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12364,cell12364,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12364 ⟨23,by decide⟩).lower ∧ (cell12364 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12364 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12364 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12364 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12364 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12364 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12364,cell12364,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12364 ⟨24,by decide⟩).lower ∧ (cell12364 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12364 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12364 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12364 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12364 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12364 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12364,cell12364,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12364 ⟨25,by decide⟩).lower ∧ (cell12364 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12364 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12364 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12364 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12364 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12364 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12364,cell12364,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12364 ⟨26,by decide⟩).lower ∧ (cell12364 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12364 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12364 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12364 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12364 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12364 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12364,cell12364,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12364 ⟨27,by decide⟩).lower ∧ (cell12364 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12364 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12364 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12364 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12364 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12364 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12364,cell12364,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12364 ⟨28,by decide⟩).lower ∧ (cell12364 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12364 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12364 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12364 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12364 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12364 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12364,cell12364,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12364 ⟨29,by decide⟩).lower ∧ (cell12364 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12364 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12364 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12364 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12364 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12364 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12364,cell12364,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12364 ⟨30,by decide⟩).lower ∧ (cell12364 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12364 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12364 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12364 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12364 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12364 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12364,cell12364,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12364 ⟨31,by decide⟩).lower ∧ (cell12364 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12364 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12364 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12364 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12364 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12364 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12364,cell12364,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12364 ⟨32,by decide⟩).lower ∧ (cell12364 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12364 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12364 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12364 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12364 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12364 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12364,cell12364,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12364 ⟨33,by decide⟩).lower ∧ (cell12364 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12364 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12364 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12364 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12364 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12364 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12364,cell12364,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12364 ⟨34,by decide⟩).lower ∧ (cell12364 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12364 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12364 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12364 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12364 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12364 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12364,cell12364,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12364 ⟨35,by decide⟩).lower ∧ (cell12364 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12364 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12364 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12364 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12364 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12364 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12364,cell12364,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12364 ⟨36,by decide⟩).lower ∧ (cell12364 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12364 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12364 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12364 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12364 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12364 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12364,cell12364,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12364 ⟨37,by decide⟩).lower ∧ (cell12364 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12364 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12364 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12364 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12364 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12364 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12364,cell12364,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12364 ⟨38,by decide⟩).lower ∧ (cell12364 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12364 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12364 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12364 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12364 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12364 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12364,cell12364,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12364 ⟨39,by decide⟩).lower ∧ (cell12364 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12364 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12364 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12364 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12364 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12364 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12364,cell12364,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12364 ⟨40,by decide⟩).lower ∧ (cell12364 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12364 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12364 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12364 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12364 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12364 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12364,cell12364,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12364 ⟨41,by decide⟩).lower ∧ (cell12364 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12364 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12364 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12364 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12364 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12364 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12364,cell12364,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12364 ⟨42,by decide⟩).lower ∧ (cell12364 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12364 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12364 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12364 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12364 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12364 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12364,cell12364,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12364 ⟨43,by decide⟩).lower ∧ (cell12364 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12364 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12364 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12364 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12364 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12364 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12364,cell12364,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12364 ⟨44,by decide⟩).lower ∧ (cell12364 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12364 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12364 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12364 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12364 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12364 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12364,cell12364,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12364 ⟨45,by decide⟩).lower ∧ (cell12364 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12364 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12364 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12364 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12364 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12364 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12364,cell12364,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12364 ⟨46,by decide⟩).lower ∧ (cell12364 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12364 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12364 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12364 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12364 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12364 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12364,cell12364,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12364 ⟨47,by decide⟩).lower ∧ (cell12364 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12364 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12364 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12364 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12364 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12364 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12364,cell12364,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12364 ⟨48,by decide⟩).lower ∧ (cell12364 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12364 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12364 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12364 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12364 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12364 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12364,cell12364,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12364 ⟨49,by decide⟩).lower ∧ (cell12364 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12364 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12364 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12364 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12364 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12364 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12364,cell12364,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12364 ⟨50,by decide⟩).lower ∧ (cell12364 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12364 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12364 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12364 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12364 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12364 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12364,cell12364,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12364 ⟨51,by decide⟩).lower ∧ (cell12364 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12364 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12364 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12364 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12364 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12364 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12364,cell12364,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12364 ⟨52,by decide⟩).lower ∧ (cell12364 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12364 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12364 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12364 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12364 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12364 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12364,cell12364,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12364 i).lower ∧
    (cell12364 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12364 i).upper ≤ (0.532 : ℝ) ∧
    (cell12364 i).centre ≤ (0.1 : ℝ) ∧ (cell12364 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12364 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12364 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12364

/-! The local source numeric instances at 12364 have no network premises. -/
namespace BstLean.Part269.N12364
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12364)
open BstLean.Part268 (cell12364)

noncomputable def sourceNumerics12364 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12364 (cell12364 i)
      scalarRow12364.M scalarRow12364.H scalarRow12364.xi := by
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
    energy_allowance := scalarRow12364.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12364]
    centre_nonneg := (scalarRow12364.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D0.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12364])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12364
/-! Actual 12365 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12365
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12365 ≤ (1.036295356754 : ℝ) := by
  have hr : (111.198021565133 : ℝ) ≤ √(12365 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.198021565133 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12365 12365 (11 / 1000) ≤
    (0.008596260214 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12365) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.198021565133 : ℝ) ≤ √(12365 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12365)
  have hdiv : K / √(12365 : ℝ) ≤ K / 111.198021565133 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.198021565133 ≤ (0.008596260214 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12365.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12365 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12365 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12365 := gPlus_lower 12365
end BstLean.Part269.N12365

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12365
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036295356753 : ℝ) ≤ wn 12365 := by
  have hn : √(12365 : ℝ) ≤ 111.198021565134 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12365 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.198021565134 ≤ 2 / √(12365 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000258826395 : ℝ) ≤ rhoBar 12365 BstLean.Part154.csC ∧
    rhoBar 12365 BstLean.Part154.csC ≤ 0.000258826795 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036295356753 : ℝ) / (1.295212 * 12365) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036295356754 : ℝ) / (1.29521 * 12365) := by gcongr
      _ ≤ (0.000258826795 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12365 BstLean.Part154.csC) ≤ 0.001035374172 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12365 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12365 BstLean.Part154.csC) (piBar (rhoBar 12365 BstLean.Part154.csC)) ≤ 0.000197693906 ∧
    cc1 (rhoBar 12365 BstLean.Part154.csC) (piBar (rhoBar 12365 BstLean.Part154.csC)) ≤ 0.000125793893 ∧
    cc2 (rhoBar 12365 BstLean.Part154.csC) ≤ 0.000073024255 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12365 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12365 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12365 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12365 BstLean.Part154.csC * nuR (rhoBar 12365 BstLean.Part154.csC)) ≤ 0.000517670338 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000258826795 : ℝ) * 0.001035374172 := by gcongr
      _ ≤ (0.000517670338 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12365 BstLean.Part154.csC) * nuR (rhoBar 12365 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001035374172 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12365 BstLean.Part154.csC) * rhoBar 12365 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000258826795 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000258826795 / 2 + 0.399 * 0.001035374172 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000197693906 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000517670338 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125793893 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000258826795 / 1.414213562 := by gcongr
      _ ≤ (0.000073024255 : ℝ) := by norm_num

end BstLean.Part269.N12365

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12365
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12365 BstLean.Part154.csC) (piBar (rhoBar 12365 BstLean.Part154.csC)) ≤ 1.68780E-7 := by
  have hr0 : 0 ≤ rhoBar 12365 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12365 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12365 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12365 BstLean.Part154.csC) (piBar (rhoBar 12365 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12365 BstLean.Part154.csC) (piBar (rhoBar 12365 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12365 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000197693906 : ℝ) ^ 2 + 0.000125793893 ^ 2 + 3 * 0.000073024255 ^ 2 +
        2 * 0.797885 * 0.000197693906 * 0.000125793893 + 2 * 0.000197693906 * 0.000073024255 +
        4 * 0.797885 * 0.000125793893 * 0.000073024255 := by gcongr
    _ ≤ (1.68780E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12365 BstLean.Part154.csC Θ ≤ 0.002703061724 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12365 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12365 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12365 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12365 BstLean.Part154.csC) (piBar (rhoBar 12365 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12365 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036295356754 * 1.68780E-7 / (0.000258826395 : ℝ) := by gcongr
    _ ≤ 0.002703061724 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12365 BstLean.Part154.csC Θ ≤ 0.003000602333 + 0.000683019325 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12365 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12365 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12365 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036295356754 : ℝ) * ((2 * Θ * 0.000258826795 +
        (6863 / 10000) * 0.000258826795 * 12365 * 0.001035374172) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003000602333 + 0.000683019325 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12365 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12365 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12365 0.011 Θ ∧ gammaRatio 12365 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12365 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036295356754 : ℝ) * 0.525 / ((1 - 0.011) * 12365) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12365 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12365 0.011 Θ) :=
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
    badAllowance 12365 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12365 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12365 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12365 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12365 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12365 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12365 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12365 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12365 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12365 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12365 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036295356754 : ℝ) * 12365 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12365 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004100602333 + 0.003386081049 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12365

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12365
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12365 BstLean.Part154.csC) (piBar (rhoBar 12365 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12365 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12365 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12365 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12365 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12365 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12365 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12365 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12365 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12365 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12365 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12365 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12365 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12365 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12365 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053198290581 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12365) ≤ 0.010739737671 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12365 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036295356754)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010739737671 + 2 * 0.737676 / 12365) := by gcongr
    _ ≤ (0.053198290581 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12365 12 ≤ 0.0015 := by
  exact BstLean.Part269.S0.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12365

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12365
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560488008152 : ℝ) ≤ plow 12365 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12365) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053384894884)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001419107406) : eMP 12365 0.011 xi bn ≤ 0.001221298527 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12365 : ℝ) * (1 - 0.011))) ≤ 0.000603792046 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001419107406 / (12365 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000603792046 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000603792046 : ℝ) + 3.141593 * 0.053384894884 / (12365 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001221298527 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053384894884)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001419107406) : PiBarMP 12365 12 0.011 xi bn ≤ 0.163444887809 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12365 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037671042009 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.584741262074 : ℝ) ≤ √((12365 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.198021565133 : ℝ) ≤ √(12365 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12365) ≤ 0.125293670397 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037671042009 + 0.053384894884 * 1.772454 / (2 * (110.584741262074 : ℝ))) * (1 + 0.001221298527) +
        8 / (12365 * 111.198021565133) + 0.125293670397 := by gcongr
    _ ≤ (0.163444887809 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053384894884)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001419107406) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284250005321) :
    parallelOracle 12365 0.011 xi bn cd ≤ 0.164465802001 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12365 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12365 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560488008152 : ℝ) ≤ plow 12365 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.198021565133 : ℝ) ≤ √(12365 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284250005321 : ℝ) / (2 * 0.560488008152 * 111.198021565133)) * 0.163444887809 +
        0.284250005321 ^ 2 / (2 * 0.560488008152 * 111.198021565133) := by gcongr
    _ ≤ (0.164465802001 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053384894884) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001419107406)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284250005321) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12365 12365 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560488008152 : ℝ) ≤ plow 12365 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.198021565133 : ℝ) ≤ √(12365 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12365 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12365 Θ 1.22 ≤ 0.011925576385 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.198021565133 := by gcongr <;> linarith
      _ ≤ (0.011925576385 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12365 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12365 12365 0.011 ≤ 0.008596260214 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12365 12365 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12365 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12365 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12365 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12365 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164465802001 + 0.011925576385 + (0.008596260214 : ℝ) *
        (1 + 2 * (0.284250005321 + 0.011925576385) / (0.560488008152 * 111.198021565133))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12365]

end BstLean.Part269.N12365

/-! The original eight local profiles supply actual 12365 moment certificates. -/
namespace BstLean.Part269.N12365
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12365 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12365 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12365 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053384894884 ∧
    0 ≤ bN 12365 BstLean.Part154.csC (groupTheta g) ∧ bN 12365 BstLean.Part154.csC (groupTheta g) ≤ 0.001419107406 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12365 12365 0.011
      (momentAllowance 12365 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12365 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12365 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12365 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12365 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12365 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231051714740 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12365 0.011
      (momentAllowance 12365 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12365 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12365
/-! The actual computed-centre upper energy formula at 12365. -/
namespace BstLean.Part269.N12365
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12365

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12365
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12365)
open BstLean.Part268 (cell12365)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086535732393
  | 2 => 0.087499333648
  | 3 => 0.088464373246
  | 4 => 0.089433008521
  | 5 => 0.090407820882
  | 6 => 0.091391875044
  | 7 => 0.092388783168
  | 8 => 0.093402773828
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12365 12365 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12365 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12365

/-! Actual upper energy certificates on all 43 source endpoints at 12365. -/
namespace BstLean.Part269.N12365
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12365)
open BstLean.Part268 (cell12365)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12365 (gMinus 12365) (1 - (cell12365 i).lower) ≤ 1 ∧
    energyUpper 12365 (gMinus 12365) (BstLean.Part211.gPlus 12365)
      (finiteEnergy 12365 12365 0.011) (1 - (cell12365 i).lower) ≤
      (cell12365 i).energy := by
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
      have E := BstLean.Part269.S0.uniformEnergy10 (n := 12365) (by norm_num)
        (q := 1 - (cell12365 ⟨10,by decide⟩).lower)
        (by norm_num [cell12365]) (by norm_num [cell12365])
      exact ⟨E.1,E.2.trans (by norm_num [cell12365])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy11 (n := 12365) (by norm_num)
        (q := 1 - (cell12365 ⟨11,by decide⟩).lower)
        (by norm_num [cell12365]) (by norm_num [cell12365])
      exact ⟨E.1,E.2.trans (by norm_num [cell12365])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy12 (n := 12365) (by norm_num)
        (q := 1 - (cell12365 ⟨12,by decide⟩).lower)
        (by norm_num [cell12365]) (by norm_num [cell12365])
      exact ⟨E.1,E.2.trans (by norm_num [cell12365])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy13 (n := 12365) (by norm_num)
        (q := 1 - (cell12365 ⟨13,by decide⟩).lower)
        (by norm_num [cell12365]) (by norm_num [cell12365])
      exact ⟨E.1,E.2.trans (by norm_num [cell12365])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy14 (n := 12365) (by norm_num)
        (q := 1 - (cell12365 ⟨14,by decide⟩).lower)
        (by norm_num [cell12365]) (by norm_num [cell12365])
      exact ⟨E.1,E.2.trans (by norm_num [cell12365])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy15 (n := 12365) (by norm_num)
        (q := 1 - (cell12365 ⟨15,by decide⟩).lower)
        (by norm_num [cell12365]) (by norm_num [cell12365])
      exact ⟨E.1,E.2.trans (by norm_num [cell12365])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy16 (n := 12365) (by norm_num)
        (q := 1 - (cell12365 ⟨16,by decide⟩).lower)
        (by norm_num [cell12365]) (by norm_num [cell12365])
      exact ⟨E.1,E.2.trans (by norm_num [cell12365])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy17 (n := 12365) (by norm_num)
        (q := 1 - (cell12365 ⟨17,by decide⟩).lower)
        (by norm_num [cell12365]) (by norm_num [cell12365])
      exact ⟨E.1,E.2.trans (by norm_num [cell12365])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy18 (n := 12365) (by norm_num)
        (q := 1 - (cell12365 ⟨18,by decide⟩).lower)
        (by norm_num [cell12365]) (by norm_num [cell12365])
      exact ⟨E.1,E.2.trans (by norm_num [cell12365])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy19 (n := 12365) (by norm_num)
        (q := 1 - (cell12365 ⟨19,by decide⟩).lower)
        (by norm_num [cell12365]) (by norm_num [cell12365])
      exact ⟨E.1,E.2.trans (by norm_num [cell12365])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy20 (n := 12365) (by norm_num)
        (q := 1 - (cell12365 ⟨20,by decide⟩).lower)
        (by norm_num [cell12365]) (by norm_num [cell12365])
      exact ⟨E.1,E.2.trans (by norm_num [cell12365])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy21 (n := 12365) (by norm_num)
        (q := 1 - (cell12365 ⟨21,by decide⟩).lower)
        (by norm_num [cell12365]) (by norm_num [cell12365])
      exact ⟨E.1,E.2.trans (by norm_num [cell12365])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy22 (n := 12365) (by norm_num)
        (q := 1 - (cell12365 ⟨22,by decide⟩).lower)
        (by norm_num [cell12365]) (by norm_num [cell12365])
      exact ⟨E.1,E.2.trans (by norm_num [cell12365])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy23 (n := 12365) (by norm_num)
        (q := 1 - (cell12365 ⟨23,by decide⟩).lower)
        (by norm_num [cell12365]) (by norm_num [cell12365])
      exact ⟨E.1,E.2.trans (by norm_num [cell12365])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy24 (n := 12365) (by norm_num)
        (q := 1 - (cell12365 ⟨24,by decide⟩).lower)
        (by norm_num [cell12365]) (by norm_num [cell12365])
      exact ⟨E.1,E.2.trans (by norm_num [cell12365])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy25 (n := 12365) (by norm_num)
        (q := 1 - (cell12365 ⟨25,by decide⟩).lower)
        (by norm_num [cell12365]) (by norm_num [cell12365])
      exact ⟨E.1,E.2.trans (by norm_num [cell12365])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy26 (n := 12365) (by norm_num)
        (q := 1 - (cell12365 ⟨26,by decide⟩).lower)
        (by norm_num [cell12365]) (by norm_num [cell12365])
      exact ⟨E.1,E.2.trans (by norm_num [cell12365])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy27 (n := 12365) (by norm_num)
        (q := 1 - (cell12365 ⟨27,by decide⟩).lower)
        (by norm_num [cell12365]) (by norm_num [cell12365])
      exact ⟨E.1,E.2.trans (by norm_num [cell12365])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy28 (n := 12365) (by norm_num)
        (q := 1 - (cell12365 ⟨28,by decide⟩).lower)
        (by norm_num [cell12365]) (by norm_num [cell12365])
      exact ⟨E.1,E.2.trans (by norm_num [cell12365])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy29 (n := 12365) (by norm_num)
        (q := 1 - (cell12365 ⟨29,by decide⟩).lower)
        (by norm_num [cell12365]) (by norm_num [cell12365])
      exact ⟨E.1,E.2.trans (by norm_num [cell12365])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy30 (n := 12365) (by norm_num)
        (q := 1 - (cell12365 ⟨30,by decide⟩).lower)
        (by norm_num [cell12365]) (by norm_num [cell12365])
      exact ⟨E.1,E.2.trans (by norm_num [cell12365])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy31 (n := 12365) (by norm_num)
        (q := 1 - (cell12365 ⟨31,by decide⟩).lower)
        (by norm_num [cell12365]) (by norm_num [cell12365])
      exact ⟨E.1,E.2.trans (by norm_num [cell12365])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy32 (n := 12365) (by norm_num)
        (q := 1 - (cell12365 ⟨32,by decide⟩).lower)
        (by norm_num [cell12365]) (by norm_num [cell12365])
      exact ⟨E.1,E.2.trans (by norm_num [cell12365])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy33 (n := 12365) (by norm_num)
        (q := 1 - (cell12365 ⟨33,by decide⟩).lower)
        (by norm_num [cell12365]) (by norm_num [cell12365])
      exact ⟨E.1,E.2.trans (by norm_num [cell12365])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy34 (n := 12365) (by norm_num)
        (q := 1 - (cell12365 ⟨34,by decide⟩).lower)
        (by norm_num [cell12365]) (by norm_num [cell12365])
      exact ⟨E.1,E.2.trans (by norm_num [cell12365])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy35 (n := 12365) (by norm_num)
        (q := 1 - (cell12365 ⟨35,by decide⟩).lower)
        (by norm_num [cell12365]) (by norm_num [cell12365])
      exact ⟨E.1,E.2.trans (by norm_num [cell12365])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy36 (n := 12365) (by norm_num)
        (q := 1 - (cell12365 ⟨36,by decide⟩).lower)
        (by norm_num [cell12365]) (by norm_num [cell12365])
      exact ⟨E.1,E.2.trans (by norm_num [cell12365])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy37 (n := 12365) (by norm_num)
        (q := 1 - (cell12365 ⟨37,by decide⟩).lower)
        (by norm_num [cell12365]) (by norm_num [cell12365])
      exact ⟨E.1,E.2.trans (by norm_num [cell12365])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy38 (n := 12365) (by norm_num)
        (q := 1 - (cell12365 ⟨38,by decide⟩).lower)
        (by norm_num [cell12365]) (by norm_num [cell12365])
      exact ⟨E.1,E.2.trans (by norm_num [cell12365])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy39 (n := 12365) (by norm_num)
        (q := 1 - (cell12365 ⟨39,by decide⟩).lower)
        (by norm_num [cell12365]) (by norm_num [cell12365])
      exact ⟨E.1,E.2.trans (by norm_num [cell12365])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy40 (n := 12365) (by norm_num)
        (q := 1 - (cell12365 ⟨40,by decide⟩).lower)
        (by norm_num [cell12365]) (by norm_num [cell12365])
      exact ⟨E.1,E.2.trans (by norm_num [cell12365])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy41 (n := 12365) (by norm_num)
        (q := 1 - (cell12365 ⟨41,by decide⟩).lower)
        (by norm_num [cell12365]) (by norm_num [cell12365])
      exact ⟨E.1,E.2.trans (by norm_num [cell12365])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy42 (n := 12365) (by norm_num)
        (q := 1 - (cell12365 ⟨42,by decide⟩).lower)
        (by norm_num [cell12365]) (by norm_num [cell12365])
      exact ⟨E.1,E.2.trans (by norm_num [cell12365])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy43 (n := 12365) (by norm_num)
        (q := 1 - (cell12365 ⟨43,by decide⟩).lower)
        (by norm_num [cell12365]) (by norm_num [cell12365])
      exact ⟨E.1,E.2.trans (by norm_num [cell12365])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy44 (n := 12365) (by norm_num)
        (q := 1 - (cell12365 ⟨44,by decide⟩).lower)
        (by norm_num [cell12365]) (by norm_num [cell12365])
      exact ⟨E.1,E.2.trans (by norm_num [cell12365])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy45 (n := 12365) (by norm_num)
        (q := 1 - (cell12365 ⟨45,by decide⟩).lower)
        (by norm_num [cell12365]) (by norm_num [cell12365])
      exact ⟨E.1,E.2.trans (by norm_num [cell12365])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy46 (n := 12365) (by norm_num)
        (q := 1 - (cell12365 ⟨46,by decide⟩).lower)
        (by norm_num [cell12365]) (by norm_num [cell12365])
      exact ⟨E.1,E.2.trans (by norm_num [cell12365])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy47 (n := 12365) (by norm_num)
        (q := 1 - (cell12365 ⟨47,by decide⟩).lower)
        (by norm_num [cell12365]) (by norm_num [cell12365])
      exact ⟨E.1,E.2.trans (by norm_num [cell12365])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy48 (n := 12365) (by norm_num)
        (q := 1 - (cell12365 ⟨48,by decide⟩).lower)
        (by norm_num [cell12365]) (by norm_num [cell12365])
      exact ⟨E.1,E.2.trans (by norm_num [cell12365])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy49 (n := 12365) (by norm_num)
        (q := 1 - (cell12365 ⟨49,by decide⟩).lower)
        (by norm_num [cell12365]) (by norm_num [cell12365])
      exact ⟨E.1,E.2.trans (by norm_num [cell12365])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy50 (n := 12365) (by norm_num)
        (q := 1 - (cell12365 ⟨50,by decide⟩).lower)
        (by norm_num [cell12365]) (by norm_num [cell12365])
      exact ⟨E.1,E.2.trans (by norm_num [cell12365])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy51 (n := 12365) (by norm_num)
        (q := 1 - (cell12365 ⟨51,by decide⟩).lower)
        (by norm_num [cell12365]) (by norm_num [cell12365])
      exact ⟨E.1,E.2.trans (by norm_num [cell12365])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy52 (n := 12365) (by norm_num)
        (q := 1 - (cell12365 ⟨52,by decide⟩).lower)
        (by norm_num [cell12365]) (by norm_num [cell12365])
      exact ⟨E.1,E.2.trans (by norm_num [cell12365])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12365

/-! Source-cell containment and simple scalar guards at 12365. -/
namespace BstLean.Part269.N12365
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12365)
open BstLean.Part268 (cell12365)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12365 ⟨10,by decide⟩).lower ∧ (cell12365 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12365 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12365 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12365 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12365 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12365 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12365,cell12365,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12365 ⟨11,by decide⟩).lower ∧ (cell12365 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12365 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12365 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12365 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12365 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12365 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12365,cell12365,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12365 ⟨12,by decide⟩).lower ∧ (cell12365 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12365 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12365 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12365 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12365 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12365 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12365,cell12365,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12365 ⟨13,by decide⟩).lower ∧ (cell12365 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12365 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12365 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12365 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12365 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12365 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12365,cell12365,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12365 ⟨14,by decide⟩).lower ∧ (cell12365 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12365 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12365 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12365 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12365 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12365 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12365,cell12365,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12365 ⟨15,by decide⟩).lower ∧ (cell12365 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12365 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12365 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12365 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12365 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12365 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12365,cell12365,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12365 ⟨16,by decide⟩).lower ∧ (cell12365 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12365 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12365 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12365 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12365 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12365 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12365,cell12365,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12365 ⟨17,by decide⟩).lower ∧ (cell12365 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12365 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12365 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12365 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12365 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12365 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12365,cell12365,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12365 ⟨18,by decide⟩).lower ∧ (cell12365 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12365 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12365 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12365 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12365 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12365 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12365,cell12365,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12365 ⟨19,by decide⟩).lower ∧ (cell12365 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12365 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12365 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12365 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12365 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12365 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12365,cell12365,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12365 ⟨20,by decide⟩).lower ∧ (cell12365 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12365 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12365 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12365 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12365 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12365 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12365,cell12365,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12365 ⟨21,by decide⟩).lower ∧ (cell12365 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12365 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12365 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12365 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12365 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12365 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12365,cell12365,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12365 ⟨22,by decide⟩).lower ∧ (cell12365 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12365 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12365 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12365 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12365 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12365 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12365,cell12365,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12365 ⟨23,by decide⟩).lower ∧ (cell12365 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12365 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12365 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12365 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12365 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12365 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12365,cell12365,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12365 ⟨24,by decide⟩).lower ∧ (cell12365 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12365 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12365 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12365 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12365 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12365 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12365,cell12365,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12365 ⟨25,by decide⟩).lower ∧ (cell12365 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12365 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12365 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12365 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12365 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12365 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12365,cell12365,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12365 ⟨26,by decide⟩).lower ∧ (cell12365 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12365 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12365 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12365 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12365 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12365 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12365,cell12365,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12365 ⟨27,by decide⟩).lower ∧ (cell12365 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12365 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12365 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12365 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12365 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12365 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12365,cell12365,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12365 ⟨28,by decide⟩).lower ∧ (cell12365 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12365 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12365 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12365 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12365 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12365 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12365,cell12365,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12365 ⟨29,by decide⟩).lower ∧ (cell12365 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12365 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12365 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12365 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12365 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12365 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12365,cell12365,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12365 ⟨30,by decide⟩).lower ∧ (cell12365 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12365 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12365 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12365 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12365 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12365 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12365,cell12365,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12365 ⟨31,by decide⟩).lower ∧ (cell12365 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12365 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12365 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12365 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12365 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12365 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12365,cell12365,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12365 ⟨32,by decide⟩).lower ∧ (cell12365 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12365 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12365 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12365 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12365 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12365 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12365,cell12365,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12365 ⟨33,by decide⟩).lower ∧ (cell12365 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12365 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12365 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12365 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12365 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12365 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12365,cell12365,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12365 ⟨34,by decide⟩).lower ∧ (cell12365 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12365 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12365 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12365 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12365 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12365 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12365,cell12365,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12365 ⟨35,by decide⟩).lower ∧ (cell12365 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12365 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12365 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12365 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12365 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12365 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12365,cell12365,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12365 ⟨36,by decide⟩).lower ∧ (cell12365 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12365 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12365 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12365 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12365 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12365 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12365,cell12365,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12365 ⟨37,by decide⟩).lower ∧ (cell12365 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12365 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12365 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12365 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12365 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12365 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12365,cell12365,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12365 ⟨38,by decide⟩).lower ∧ (cell12365 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12365 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12365 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12365 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12365 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12365 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12365,cell12365,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12365 ⟨39,by decide⟩).lower ∧ (cell12365 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12365 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12365 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12365 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12365 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12365 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12365,cell12365,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12365 ⟨40,by decide⟩).lower ∧ (cell12365 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12365 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12365 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12365 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12365 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12365 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12365,cell12365,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12365 ⟨41,by decide⟩).lower ∧ (cell12365 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12365 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12365 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12365 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12365 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12365 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12365,cell12365,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12365 ⟨42,by decide⟩).lower ∧ (cell12365 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12365 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12365 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12365 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12365 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12365 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12365,cell12365,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12365 ⟨43,by decide⟩).lower ∧ (cell12365 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12365 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12365 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12365 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12365 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12365 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12365,cell12365,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12365 ⟨44,by decide⟩).lower ∧ (cell12365 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12365 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12365 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12365 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12365 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12365 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12365,cell12365,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12365 ⟨45,by decide⟩).lower ∧ (cell12365 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12365 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12365 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12365 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12365 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12365 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12365,cell12365,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12365 ⟨46,by decide⟩).lower ∧ (cell12365 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12365 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12365 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12365 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12365 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12365 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12365,cell12365,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12365 ⟨47,by decide⟩).lower ∧ (cell12365 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12365 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12365 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12365 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12365 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12365 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12365,cell12365,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12365 ⟨48,by decide⟩).lower ∧ (cell12365 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12365 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12365 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12365 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12365 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12365 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12365,cell12365,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12365 ⟨49,by decide⟩).lower ∧ (cell12365 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12365 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12365 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12365 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12365 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12365 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12365,cell12365,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12365 ⟨50,by decide⟩).lower ∧ (cell12365 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12365 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12365 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12365 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12365 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12365 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12365,cell12365,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12365 ⟨51,by decide⟩).lower ∧ (cell12365 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12365 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12365 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12365 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12365 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12365 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12365,cell12365,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12365 ⟨52,by decide⟩).lower ∧ (cell12365 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12365 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12365 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12365 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12365 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12365 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12365,cell12365,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12365 i).lower ∧
    (cell12365 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12365 i).upper ≤ (0.532 : ℝ) ∧
    (cell12365 i).centre ≤ (0.1 : ℝ) ∧ (cell12365 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12365 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12365 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12365

/-! The local source numeric instances at 12365 have no network premises. -/
namespace BstLean.Part269.N12365
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12365)
open BstLean.Part268 (cell12365)

noncomputable def sourceNumerics12365 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12365 (cell12365 i)
      scalarRow12365.M scalarRow12365.H scalarRow12365.xi := by
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
    energy_allowance := scalarRow12365.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12365]
    centre_nonneg := (scalarRow12365.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D0.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12365])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12365
/-! Actual 12366 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12366
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12366 ≤ (1.036293876099 : ℝ) := by
  have hr : (111.202517957103 : ℝ) ≤ √(12366 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.202517957103 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12366 12366 (11 / 1000) ≤
    (0.008595912628 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12366) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.202517957103 : ℝ) ≤ √(12366 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12366)
  have hdiv : K / √(12366 : ℝ) ≤ K / 111.202517957103 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.202517957103 ≤ (0.008595912628 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12366.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12366 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12366 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12366 := gPlus_lower 12366
end BstLean.Part269.N12366

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12366
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036293876098 : ℝ) ≤ wn 12366 := by
  have hn : √(12366 : ℝ) ≤ 111.202517957104 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12366 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.202517957104 ≤ 2 / √(12366 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000258805094 : ℝ) ≤ rhoBar 12366 BstLean.Part154.csC ∧
    rhoBar 12366 BstLean.Part154.csC ≤ 0.000258805495 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036293876098 : ℝ) / (1.295212 * 12366) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036293876099 : ℝ) / (1.29521 * 12366) := by gcongr
      _ ≤ (0.000258805495 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12366 BstLean.Part154.csC) ≤ 0.001035288961 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12366 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12366 BstLean.Part154.csC) (piBar (rhoBar 12366 BstLean.Part154.csC)) ≤ 0.000197677636 ∧
    cc1 (rhoBar 12366 BstLean.Part154.csC) (piBar (rhoBar 12366 BstLean.Part154.csC)) ≤ 0.000125783540 ∧
    cc2 (rhoBar 12366 BstLean.Part154.csC) ≤ 0.000073018246 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12366 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12366 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12366 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12366 BstLean.Part154.csC * nuR (rhoBar 12366 BstLean.Part154.csC)) ≤ 0.000517627735 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000258805495 : ℝ) * 0.001035288961 := by gcongr
      _ ≤ (0.000517627735 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12366 BstLean.Part154.csC) * nuR (rhoBar 12366 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001035288961 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12366 BstLean.Part154.csC) * rhoBar 12366 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000258805495 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000258805495 / 2 + 0.399 * 0.001035288961 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000197677636 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000517627735 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125783540 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000258805495 / 1.414213562 := by gcongr
      _ ≤ (0.000073018246 : ℝ) := by norm_num

end BstLean.Part269.N12366

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12366
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12366 BstLean.Part154.csC) (piBar (rhoBar 12366 BstLean.Part154.csC)) ≤ 1.68752E-7 := by
  have hr0 : 0 ≤ rhoBar 12366 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12366 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12366 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12366 BstLean.Part154.csC) (piBar (rhoBar 12366 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12366 BstLean.Part154.csC) (piBar (rhoBar 12366 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12366 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000197677636 : ℝ) ^ 2 + 0.000125783540 ^ 2 + 3 * 0.000073018246 ^ 2 +
        2 * 0.797885 * 0.000197677636 * 0.000125783540 + 2 * 0.000197677636 * 0.000073018246 +
        4 * 0.797885 * 0.000125783540 * 0.000073018246 := by gcongr
    _ ≤ (1.68752E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12366 BstLean.Part154.csC Θ ≤ 0.002702831873 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12366 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12366 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12366 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12366 BstLean.Part154.csC) (piBar (rhoBar 12366 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12366 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036293876099 * 1.68752E-7 / (0.000258805094 : ℝ) := by gcongr
    _ ≤ 0.002702831873 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12366 BstLean.Part154.csC Θ ≤ 0.003000346814 + 0.000682962141 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12366 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12366 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12366 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036293876099 : ℝ) * ((2 * Θ * 0.000258805495 +
        (6863 / 10000) * 0.000258805495 * 12366 * 0.001035288961) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003000346814 + 0.000682962141 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12366 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12366 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12366 0.011 Θ ∧ gammaRatio 12366 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12366 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036293876099 : ℝ) * 0.525 / ((1 - 0.011) * 12366) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12366 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12366 0.011 Θ) :=
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
    badAllowance 12366 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12366 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12366 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12366 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12366 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12366 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12366 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12366 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12366 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12366 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12366 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036293876099 : ℝ) * 12366 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12366 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004100346814 + 0.003385794014 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12366

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12366
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12366 BstLean.Part154.csC) (piBar (rhoBar 12366 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12366 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12366 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12366 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12366 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12366 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12366 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12366 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12366 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12366 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12366 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12366 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12366 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12366 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12366 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053196115910 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12366) ≤ 0.010739303417 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12366 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036293876099)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010739303417 + 2 * 0.737676 / 12366) := by gcongr
    _ ≤ (0.053196115910 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12366 12 ≤ 0.0015 := by
  exact BstLean.Part269.S0.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12366

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12366
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560488055854 : ℝ) ≤ plow 12366 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12366) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053384488672)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001418986734) : eMP 12366 0.011 xi bn ≤ 0.001221197145 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12366 : ℝ) * (1 - 0.011))) ≤ 0.000603741962 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001418986734 / (12366 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000603741962 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000603741962 : ℝ) + 3.141593 * 0.053384488672 / (12366 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001221197145 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053384488672)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001418986734) : PiBarMP 12366 12 0.011 xi bn ≤ 0.163438192860 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12366 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037669440320 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.589212855504 : ℝ) ≤ √((12366 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.202517957103 : ℝ) ≤ √(12366 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12366) ≤ 0.125288604240 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037669440320 + 0.053384488672 * 1.772454 / (2 * (110.589212855504 : ℝ))) * (1 + 0.001221197145) +
        8 / (12366 * 111.202517957103) + 0.125288604240 := by gcongr
    _ ≤ (0.163438192860 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053384488672)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001418986734) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284246951598) :
    parallelOracle 12366 0.011 xi bn cd ≤ 0.164459032488 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12366 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12366 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560488055854 : ℝ) ≤ plow 12366 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.202517957103 : ℝ) ≤ √(12366 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284246951598 : ℝ) / (2 * 0.560488055854 * 111.202517957103)) * 0.163438192860 +
        0.284246951598 ^ 2 / (2 * 0.560488055854 * 111.202517957103) := by gcongr
    _ ≤ (0.164459032488 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053384488672) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001418986734)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284246951598) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12366 12366 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560488055854 : ℝ) ≤ plow 12366 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.202517957103 : ℝ) ≤ √(12366 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12366 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12366 Θ 1.22 ≤ 0.011925094183 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.202517957103 := by gcongr <;> linarith
      _ ≤ (0.011925094183 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12366 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12366 12366 0.011 ≤ 0.008595912628 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12366 12366 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12366 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12366 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12366 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12366 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164459032488 + 0.011925094183 + (0.008595912628 : ℝ) *
        (1 + 2 * (0.284246951598 + 0.011925094183) / (0.560488055854 * 111.202517957103))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12366]

end BstLean.Part269.N12366

/-! The original eight local profiles supply actual 12366 moment certificates. -/
namespace BstLean.Part269.N12366
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12366 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12366 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12366 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053384488672 ∧
    0 ≤ bN 12366 BstLean.Part154.csC (groupTheta g) ∧ bN 12366 BstLean.Part154.csC (groupTheta g) ≤ 0.001418986734 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12366 12366 0.011
      (momentAllowance 12366 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12366 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12366 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12366 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12366 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12366 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231050835688 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12366 0.011
      (momentAllowance 12366 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12366 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12366
/-! The actual computed-centre upper energy formula at 12366. -/
namespace BstLean.Part269.N12366
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12366

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12366
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12366)
open BstLean.Part268 (cell12366)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086532382176
  | 2 => 0.087495911193
  | 3 => 0.088460866373
  | 4 => 0.089429402384
  | 5 => 0.090404097521
  | 6 => 0.091388012891
  | 7 => 0.092384756494
  | 8 => 0.093398552139
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12366 12366 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12366 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12366

/-! Actual upper energy certificates on all 43 source endpoints at 12366. -/
namespace BstLean.Part269.N12366
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12366)
open BstLean.Part268 (cell12366)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12366 (gMinus 12366) (1 - (cell12366 i).lower) ≤ 1 ∧
    energyUpper 12366 (gMinus 12366) (BstLean.Part211.gPlus 12366)
      (finiteEnergy 12366 12366 0.011) (1 - (cell12366 i).lower) ≤
      (cell12366 i).energy := by
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
      have E := BstLean.Part269.S0.uniformEnergy10 (n := 12366) (by norm_num)
        (q := 1 - (cell12366 ⟨10,by decide⟩).lower)
        (by norm_num [cell12366]) (by norm_num [cell12366])
      exact ⟨E.1,E.2.trans (by norm_num [cell12366])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy11 (n := 12366) (by norm_num)
        (q := 1 - (cell12366 ⟨11,by decide⟩).lower)
        (by norm_num [cell12366]) (by norm_num [cell12366])
      exact ⟨E.1,E.2.trans (by norm_num [cell12366])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy12 (n := 12366) (by norm_num)
        (q := 1 - (cell12366 ⟨12,by decide⟩).lower)
        (by norm_num [cell12366]) (by norm_num [cell12366])
      exact ⟨E.1,E.2.trans (by norm_num [cell12366])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy13 (n := 12366) (by norm_num)
        (q := 1 - (cell12366 ⟨13,by decide⟩).lower)
        (by norm_num [cell12366]) (by norm_num [cell12366])
      exact ⟨E.1,E.2.trans (by norm_num [cell12366])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy14 (n := 12366) (by norm_num)
        (q := 1 - (cell12366 ⟨14,by decide⟩).lower)
        (by norm_num [cell12366]) (by norm_num [cell12366])
      exact ⟨E.1,E.2.trans (by norm_num [cell12366])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy15 (n := 12366) (by norm_num)
        (q := 1 - (cell12366 ⟨15,by decide⟩).lower)
        (by norm_num [cell12366]) (by norm_num [cell12366])
      exact ⟨E.1,E.2.trans (by norm_num [cell12366])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy16 (n := 12366) (by norm_num)
        (q := 1 - (cell12366 ⟨16,by decide⟩).lower)
        (by norm_num [cell12366]) (by norm_num [cell12366])
      exact ⟨E.1,E.2.trans (by norm_num [cell12366])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy17 (n := 12366) (by norm_num)
        (q := 1 - (cell12366 ⟨17,by decide⟩).lower)
        (by norm_num [cell12366]) (by norm_num [cell12366])
      exact ⟨E.1,E.2.trans (by norm_num [cell12366])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy18 (n := 12366) (by norm_num)
        (q := 1 - (cell12366 ⟨18,by decide⟩).lower)
        (by norm_num [cell12366]) (by norm_num [cell12366])
      exact ⟨E.1,E.2.trans (by norm_num [cell12366])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy19 (n := 12366) (by norm_num)
        (q := 1 - (cell12366 ⟨19,by decide⟩).lower)
        (by norm_num [cell12366]) (by norm_num [cell12366])
      exact ⟨E.1,E.2.trans (by norm_num [cell12366])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy20 (n := 12366) (by norm_num)
        (q := 1 - (cell12366 ⟨20,by decide⟩).lower)
        (by norm_num [cell12366]) (by norm_num [cell12366])
      exact ⟨E.1,E.2.trans (by norm_num [cell12366])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy21 (n := 12366) (by norm_num)
        (q := 1 - (cell12366 ⟨21,by decide⟩).lower)
        (by norm_num [cell12366]) (by norm_num [cell12366])
      exact ⟨E.1,E.2.trans (by norm_num [cell12366])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy22 (n := 12366) (by norm_num)
        (q := 1 - (cell12366 ⟨22,by decide⟩).lower)
        (by norm_num [cell12366]) (by norm_num [cell12366])
      exact ⟨E.1,E.2.trans (by norm_num [cell12366])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy23 (n := 12366) (by norm_num)
        (q := 1 - (cell12366 ⟨23,by decide⟩).lower)
        (by norm_num [cell12366]) (by norm_num [cell12366])
      exact ⟨E.1,E.2.trans (by norm_num [cell12366])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy24 (n := 12366) (by norm_num)
        (q := 1 - (cell12366 ⟨24,by decide⟩).lower)
        (by norm_num [cell12366]) (by norm_num [cell12366])
      exact ⟨E.1,E.2.trans (by norm_num [cell12366])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy25 (n := 12366) (by norm_num)
        (q := 1 - (cell12366 ⟨25,by decide⟩).lower)
        (by norm_num [cell12366]) (by norm_num [cell12366])
      exact ⟨E.1,E.2.trans (by norm_num [cell12366])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy26 (n := 12366) (by norm_num)
        (q := 1 - (cell12366 ⟨26,by decide⟩).lower)
        (by norm_num [cell12366]) (by norm_num [cell12366])
      exact ⟨E.1,E.2.trans (by norm_num [cell12366])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy27 (n := 12366) (by norm_num)
        (q := 1 - (cell12366 ⟨27,by decide⟩).lower)
        (by norm_num [cell12366]) (by norm_num [cell12366])
      exact ⟨E.1,E.2.trans (by norm_num [cell12366])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy28 (n := 12366) (by norm_num)
        (q := 1 - (cell12366 ⟨28,by decide⟩).lower)
        (by norm_num [cell12366]) (by norm_num [cell12366])
      exact ⟨E.1,E.2.trans (by norm_num [cell12366])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy29 (n := 12366) (by norm_num)
        (q := 1 - (cell12366 ⟨29,by decide⟩).lower)
        (by norm_num [cell12366]) (by norm_num [cell12366])
      exact ⟨E.1,E.2.trans (by norm_num [cell12366])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy30 (n := 12366) (by norm_num)
        (q := 1 - (cell12366 ⟨30,by decide⟩).lower)
        (by norm_num [cell12366]) (by norm_num [cell12366])
      exact ⟨E.1,E.2.trans (by norm_num [cell12366])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy31 (n := 12366) (by norm_num)
        (q := 1 - (cell12366 ⟨31,by decide⟩).lower)
        (by norm_num [cell12366]) (by norm_num [cell12366])
      exact ⟨E.1,E.2.trans (by norm_num [cell12366])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy32 (n := 12366) (by norm_num)
        (q := 1 - (cell12366 ⟨32,by decide⟩).lower)
        (by norm_num [cell12366]) (by norm_num [cell12366])
      exact ⟨E.1,E.2.trans (by norm_num [cell12366])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy33 (n := 12366) (by norm_num)
        (q := 1 - (cell12366 ⟨33,by decide⟩).lower)
        (by norm_num [cell12366]) (by norm_num [cell12366])
      exact ⟨E.1,E.2.trans (by norm_num [cell12366])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy34 (n := 12366) (by norm_num)
        (q := 1 - (cell12366 ⟨34,by decide⟩).lower)
        (by norm_num [cell12366]) (by norm_num [cell12366])
      exact ⟨E.1,E.2.trans (by norm_num [cell12366])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy35 (n := 12366) (by norm_num)
        (q := 1 - (cell12366 ⟨35,by decide⟩).lower)
        (by norm_num [cell12366]) (by norm_num [cell12366])
      exact ⟨E.1,E.2.trans (by norm_num [cell12366])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy36 (n := 12366) (by norm_num)
        (q := 1 - (cell12366 ⟨36,by decide⟩).lower)
        (by norm_num [cell12366]) (by norm_num [cell12366])
      exact ⟨E.1,E.2.trans (by norm_num [cell12366])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy37 (n := 12366) (by norm_num)
        (q := 1 - (cell12366 ⟨37,by decide⟩).lower)
        (by norm_num [cell12366]) (by norm_num [cell12366])
      exact ⟨E.1,E.2.trans (by norm_num [cell12366])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy38 (n := 12366) (by norm_num)
        (q := 1 - (cell12366 ⟨38,by decide⟩).lower)
        (by norm_num [cell12366]) (by norm_num [cell12366])
      exact ⟨E.1,E.2.trans (by norm_num [cell12366])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy39 (n := 12366) (by norm_num)
        (q := 1 - (cell12366 ⟨39,by decide⟩).lower)
        (by norm_num [cell12366]) (by norm_num [cell12366])
      exact ⟨E.1,E.2.trans (by norm_num [cell12366])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy40 (n := 12366) (by norm_num)
        (q := 1 - (cell12366 ⟨40,by decide⟩).lower)
        (by norm_num [cell12366]) (by norm_num [cell12366])
      exact ⟨E.1,E.2.trans (by norm_num [cell12366])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy41 (n := 12366) (by norm_num)
        (q := 1 - (cell12366 ⟨41,by decide⟩).lower)
        (by norm_num [cell12366]) (by norm_num [cell12366])
      exact ⟨E.1,E.2.trans (by norm_num [cell12366])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy42 (n := 12366) (by norm_num)
        (q := 1 - (cell12366 ⟨42,by decide⟩).lower)
        (by norm_num [cell12366]) (by norm_num [cell12366])
      exact ⟨E.1,E.2.trans (by norm_num [cell12366])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy43 (n := 12366) (by norm_num)
        (q := 1 - (cell12366 ⟨43,by decide⟩).lower)
        (by norm_num [cell12366]) (by norm_num [cell12366])
      exact ⟨E.1,E.2.trans (by norm_num [cell12366])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy44 (n := 12366) (by norm_num)
        (q := 1 - (cell12366 ⟨44,by decide⟩).lower)
        (by norm_num [cell12366]) (by norm_num [cell12366])
      exact ⟨E.1,E.2.trans (by norm_num [cell12366])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy45 (n := 12366) (by norm_num)
        (q := 1 - (cell12366 ⟨45,by decide⟩).lower)
        (by norm_num [cell12366]) (by norm_num [cell12366])
      exact ⟨E.1,E.2.trans (by norm_num [cell12366])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy46 (n := 12366) (by norm_num)
        (q := 1 - (cell12366 ⟨46,by decide⟩).lower)
        (by norm_num [cell12366]) (by norm_num [cell12366])
      exact ⟨E.1,E.2.trans (by norm_num [cell12366])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy47 (n := 12366) (by norm_num)
        (q := 1 - (cell12366 ⟨47,by decide⟩).lower)
        (by norm_num [cell12366]) (by norm_num [cell12366])
      exact ⟨E.1,E.2.trans (by norm_num [cell12366])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy48 (n := 12366) (by norm_num)
        (q := 1 - (cell12366 ⟨48,by decide⟩).lower)
        (by norm_num [cell12366]) (by norm_num [cell12366])
      exact ⟨E.1,E.2.trans (by norm_num [cell12366])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy49 (n := 12366) (by norm_num)
        (q := 1 - (cell12366 ⟨49,by decide⟩).lower)
        (by norm_num [cell12366]) (by norm_num [cell12366])
      exact ⟨E.1,E.2.trans (by norm_num [cell12366])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy50 (n := 12366) (by norm_num)
        (q := 1 - (cell12366 ⟨50,by decide⟩).lower)
        (by norm_num [cell12366]) (by norm_num [cell12366])
      exact ⟨E.1,E.2.trans (by norm_num [cell12366])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy51 (n := 12366) (by norm_num)
        (q := 1 - (cell12366 ⟨51,by decide⟩).lower)
        (by norm_num [cell12366]) (by norm_num [cell12366])
      exact ⟨E.1,E.2.trans (by norm_num [cell12366])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy52 (n := 12366) (by norm_num)
        (q := 1 - (cell12366 ⟨52,by decide⟩).lower)
        (by norm_num [cell12366]) (by norm_num [cell12366])
      exact ⟨E.1,E.2.trans (by norm_num [cell12366])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12366

/-! Source-cell containment and simple scalar guards at 12366. -/
namespace BstLean.Part269.N12366
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12366)
open BstLean.Part268 (cell12366)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12366 ⟨10,by decide⟩).lower ∧ (cell12366 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12366 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12366 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12366 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12366 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12366 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12366,cell12366,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12366 ⟨11,by decide⟩).lower ∧ (cell12366 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12366 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12366 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12366 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12366 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12366 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12366,cell12366,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12366 ⟨12,by decide⟩).lower ∧ (cell12366 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12366 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12366 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12366 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12366 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12366 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12366,cell12366,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12366 ⟨13,by decide⟩).lower ∧ (cell12366 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12366 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12366 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12366 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12366 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12366 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12366,cell12366,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12366 ⟨14,by decide⟩).lower ∧ (cell12366 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12366 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12366 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12366 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12366 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12366 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12366,cell12366,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12366 ⟨15,by decide⟩).lower ∧ (cell12366 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12366 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12366 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12366 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12366 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12366 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12366,cell12366,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12366 ⟨16,by decide⟩).lower ∧ (cell12366 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12366 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12366 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12366 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12366 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12366 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12366,cell12366,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12366 ⟨17,by decide⟩).lower ∧ (cell12366 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12366 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12366 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12366 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12366 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12366 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12366,cell12366,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12366 ⟨18,by decide⟩).lower ∧ (cell12366 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12366 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12366 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12366 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12366 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12366 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12366,cell12366,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12366 ⟨19,by decide⟩).lower ∧ (cell12366 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12366 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12366 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12366 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12366 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12366 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12366,cell12366,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12366 ⟨20,by decide⟩).lower ∧ (cell12366 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12366 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12366 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12366 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12366 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12366 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12366,cell12366,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12366 ⟨21,by decide⟩).lower ∧ (cell12366 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12366 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12366 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12366 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12366 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12366 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12366,cell12366,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12366 ⟨22,by decide⟩).lower ∧ (cell12366 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12366 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12366 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12366 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12366 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12366 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12366,cell12366,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12366 ⟨23,by decide⟩).lower ∧ (cell12366 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12366 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12366 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12366 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12366 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12366 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12366,cell12366,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12366 ⟨24,by decide⟩).lower ∧ (cell12366 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12366 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12366 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12366 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12366 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12366 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12366,cell12366,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12366 ⟨25,by decide⟩).lower ∧ (cell12366 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12366 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12366 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12366 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12366 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12366 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12366,cell12366,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12366 ⟨26,by decide⟩).lower ∧ (cell12366 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12366 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12366 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12366 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12366 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12366 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12366,cell12366,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12366 ⟨27,by decide⟩).lower ∧ (cell12366 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12366 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12366 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12366 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12366 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12366 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12366,cell12366,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12366 ⟨28,by decide⟩).lower ∧ (cell12366 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12366 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12366 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12366 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12366 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12366 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12366,cell12366,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12366 ⟨29,by decide⟩).lower ∧ (cell12366 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12366 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12366 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12366 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12366 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12366 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12366,cell12366,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12366 ⟨30,by decide⟩).lower ∧ (cell12366 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12366 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12366 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12366 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12366 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12366 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12366,cell12366,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12366 ⟨31,by decide⟩).lower ∧ (cell12366 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12366 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12366 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12366 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12366 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12366 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12366,cell12366,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12366 ⟨32,by decide⟩).lower ∧ (cell12366 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12366 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12366 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12366 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12366 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12366 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12366,cell12366,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12366 ⟨33,by decide⟩).lower ∧ (cell12366 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12366 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12366 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12366 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12366 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12366 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12366,cell12366,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12366 ⟨34,by decide⟩).lower ∧ (cell12366 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12366 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12366 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12366 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12366 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12366 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12366,cell12366,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12366 ⟨35,by decide⟩).lower ∧ (cell12366 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12366 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12366 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12366 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12366 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12366 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12366,cell12366,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12366 ⟨36,by decide⟩).lower ∧ (cell12366 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12366 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12366 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12366 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12366 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12366 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12366,cell12366,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12366 ⟨37,by decide⟩).lower ∧ (cell12366 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12366 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12366 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12366 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12366 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12366 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12366,cell12366,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12366 ⟨38,by decide⟩).lower ∧ (cell12366 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12366 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12366 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12366 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12366 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12366 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12366,cell12366,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12366 ⟨39,by decide⟩).lower ∧ (cell12366 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12366 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12366 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12366 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12366 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12366 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12366,cell12366,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12366 ⟨40,by decide⟩).lower ∧ (cell12366 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12366 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12366 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12366 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12366 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12366 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12366,cell12366,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12366 ⟨41,by decide⟩).lower ∧ (cell12366 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12366 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12366 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12366 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12366 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12366 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12366,cell12366,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12366 ⟨42,by decide⟩).lower ∧ (cell12366 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12366 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12366 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12366 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12366 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12366 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12366,cell12366,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12366 ⟨43,by decide⟩).lower ∧ (cell12366 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12366 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12366 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12366 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12366 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12366 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12366,cell12366,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12366 ⟨44,by decide⟩).lower ∧ (cell12366 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12366 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12366 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12366 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12366 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12366 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12366,cell12366,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12366 ⟨45,by decide⟩).lower ∧ (cell12366 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12366 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12366 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12366 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12366 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12366 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12366,cell12366,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12366 ⟨46,by decide⟩).lower ∧ (cell12366 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12366 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12366 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12366 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12366 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12366 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12366,cell12366,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12366 ⟨47,by decide⟩).lower ∧ (cell12366 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12366 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12366 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12366 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12366 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12366 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12366,cell12366,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12366 ⟨48,by decide⟩).lower ∧ (cell12366 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12366 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12366 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12366 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12366 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12366 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12366,cell12366,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12366 ⟨49,by decide⟩).lower ∧ (cell12366 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12366 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12366 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12366 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12366 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12366 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12366,cell12366,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12366 ⟨50,by decide⟩).lower ∧ (cell12366 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12366 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12366 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12366 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12366 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12366 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12366,cell12366,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12366 ⟨51,by decide⟩).lower ∧ (cell12366 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12366 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12366 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12366 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12366 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12366 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12366,cell12366,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12366 ⟨52,by decide⟩).lower ∧ (cell12366 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12366 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12366 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12366 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12366 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12366 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12366,cell12366,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12366 i).lower ∧
    (cell12366 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12366 i).upper ≤ (0.532 : ℝ) ∧
    (cell12366 i).centre ≤ (0.1 : ℝ) ∧ (cell12366 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12366 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12366 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12366

/-! The local source numeric instances at 12366 have no network premises. -/
namespace BstLean.Part269.N12366
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12366)
open BstLean.Part268 (cell12366)

noncomputable def sourceNumerics12366 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12366 (cell12366 i)
      scalarRow12366.M scalarRow12366.H scalarRow12366.xi := by
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
    energy_allowance := scalarRow12366.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12366]
    centre_nonneg := (scalarRow12366.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D0.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12366])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12366
/-! Actual 12367 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12367
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12367 ≤ (1.036292395623 : ℝ) := by
  have hr : (111.207014167272 : ℝ) ≤ √(12367 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.207014167272 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12367 12367 (11 / 1000) ≤
    (0.008595565084 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12367) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.207014167272 : ℝ) ≤ √(12367 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12367)
  have hdiv : K / √(12367 : ℝ) ≤ K / 111.207014167272 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.207014167272 ≤ (0.008595565084 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12367.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12367 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12367 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12367 := gPlus_lower 12367
end BstLean.Part269.N12367

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12367
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036292395622 : ℝ) ≤ wn 12367 := by
  have hn : √(12367 : ℝ) ≤ 111.207014167273 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12367 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.207014167273 ≤ 2 / √(12367 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000258783797 : ℝ) ≤ rhoBar 12367 BstLean.Part154.csC ∧
    rhoBar 12367 BstLean.Part154.csC ≤ 0.000258784198 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036292395622 : ℝ) / (1.295212 * 12367) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036292395623 : ℝ) / (1.29521 * 12367) := by gcongr
      _ ≤ (0.000258784198 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12367 BstLean.Part154.csC) ≤ 0.001035203762 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12367 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12367 BstLean.Part154.csC) (piBar (rhoBar 12367 BstLean.Part154.csC)) ≤ 0.000197661368 ∧
    cc1 (rhoBar 12367 BstLean.Part154.csC) (piBar (rhoBar 12367 BstLean.Part154.csC)) ≤ 0.000125773189 ∧
    cc2 (rhoBar 12367 BstLean.Part154.csC) ≤ 0.000073012237 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12367 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12367 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12367 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12367 BstLean.Part154.csC * nuR (rhoBar 12367 BstLean.Part154.csC)) ≤ 0.000517585139 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000258784198 : ℝ) * 0.001035203762 := by gcongr
      _ ≤ (0.000517585139 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12367 BstLean.Part154.csC) * nuR (rhoBar 12367 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001035203762 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12367 BstLean.Part154.csC) * rhoBar 12367 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000258784198 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000258784198 / 2 + 0.399 * 0.001035203762 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000197661368 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000517585139 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125773189 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000258784198 / 1.414213562 := by gcongr
      _ ≤ (0.000073012237 : ℝ) := by norm_num

end BstLean.Part269.N12367

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12367
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12367 BstLean.Part154.csC) (piBar (rhoBar 12367 BstLean.Part154.csC)) ≤ 1.68725E-7 := by
  have hr0 : 0 ≤ rhoBar 12367 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12367 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12367 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12367 BstLean.Part154.csC) (piBar (rhoBar 12367 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12367 BstLean.Part154.csC) (piBar (rhoBar 12367 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12367 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000197661368 : ℝ) ^ 2 + 0.000125773189 ^ 2 + 3 * 0.000073012237 ^ 2 +
        2 * 0.797885 * 0.000197661368 * 0.000125773189 + 2 * 0.000197661368 * 0.000073012237 +
        4 * 0.797885 * 0.000125773189 * 0.000073012237 := by gcongr
    _ ≤ (1.68725E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12367 BstLean.Part154.csC Θ ≤ 0.002702617962 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12367 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12367 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12367 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12367 BstLean.Part154.csC) (piBar (rhoBar 12367 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12367 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036292395623 * 1.68725E-7 / (0.000258783797 : ℝ) := by gcongr
    _ ≤ 0.002702617962 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12367 BstLean.Part154.csC Θ ≤ 0.003000091326 + 0.000682904965 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12367 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12367 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12367 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036292395623 : ℝ) * ((2 * Θ * 0.000258784198 +
        (6863 / 10000) * 0.000258784198 * 12367 * 0.001035203762) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003000091326 + 0.000682904965 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12367 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12367 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12367 0.011 Θ ∧ gammaRatio 12367 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12367 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036292395623 : ℝ) * 0.525 / ((1 - 0.011) * 12367) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12367 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12367 0.011 Θ) :=
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
    badAllowance 12367 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12367 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12367 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12367 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12367 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12367 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12367 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12367 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12367 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12367 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12367 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036292395623 : ℝ) * 12367 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12367 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004100091326 + 0.003385522927 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12367

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12367
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12367 BstLean.Part154.csC) (piBar (rhoBar 12367 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12367 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12367 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12367 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12367 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12367 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12367 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12367 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12367 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12367 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12367 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12367 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12367 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12367 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12367 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053193941511 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12367) ≤ 0.010738869217 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12367 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036292395623)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010738869217 + 2 * 0.737676 / 12367) := by gcongr
    _ ≤ (0.053193941511 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12367 12 ≤ 0.0015 := by
  exact BstLean.Part269.S0.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12367

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12367
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560488103549 : ℝ) ≤ plow 12367 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12367) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053384090863)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001418874431) : eMP 12367 0.011 xi bn ≤ 0.001221099332 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12367 : ℝ) * (1 - 0.011))) ≤ 0.000603693661 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001418874431 / (12367 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000603693661 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000603693661 : ℝ) + 3.141593 * 0.053384090863 / (12367 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001221099332 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053384090863)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001418874431) : PiBarMP 12367 12 0.011 xi bn ≤ 0.163431609888 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12367 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037667949653 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.593684268135 : ℝ) ≤ √((12367 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.207014167272 : ℝ) ≤ √(12367 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12367) ≤ 0.125283538697 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037667949653 + 0.053384090863 * 1.772454 / (2 * (110.593684268135 : ℝ))) * (1 + 0.001221099332) +
        8 / (12367 * 111.207014167272) + 0.125283538697 := by gcongr
    _ ≤ (0.163431609888 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053384090863)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001418874431) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284243916329) :
    parallelOracle 12367 0.011 xi bn cd ≤ 0.164452375324 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12367 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12367 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560488103549 : ℝ) ≤ plow 12367 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.207014167272 : ℝ) ≤ √(12367 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284243916329 : ℝ) / (2 * 0.560488103549 * 111.207014167272)) * 0.163431609888 +
        0.284243916329 ^ 2 / (2 * 0.560488103549 * 111.207014167272) := by gcongr
    _ ≤ (0.164452375324 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053384090863) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001418874431)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284243916329) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12367 12367 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560488103549 : ℝ) ≤ plow 12367 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.207014167272 : ℝ) ≤ √(12367 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12367 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12367 Θ 1.22 ≤ 0.011924612040 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.207014167272 := by gcongr <;> linarith
      _ ≤ (0.011924612040 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12367 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12367 12367 0.011 ≤ 0.008595565084 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12367 12367 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12367 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12367 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12367 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12367 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164452375324 + 0.011924612040 + (0.008595565084 : ℝ) *
        (1 + 2 * (0.284243916329 + 0.011924612040) / (0.560488103549 * 111.207014167272))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12367]

end BstLean.Part269.N12367

/-! The original eight local profiles supply actual 12367 moment certificates. -/
namespace BstLean.Part269.N12367
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12367 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12367 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12367 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053384090863 ∧
    0 ≤ bN 12367 BstLean.Part154.csC (groupTheta g) ∧ bN 12367 BstLean.Part154.csC (groupTheta g) ≤ 0.001418874431 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12367 12367 0.011
      (momentAllowance 12367 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12367 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12367 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12367 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12367 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12367 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231049974818 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12367 0.011
      (momentAllowance 12367 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12367 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12367
/-! The actual computed-centre upper energy formula at 12367. -/
namespace BstLean.Part269.N12367
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12367

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12367
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12367)
open BstLean.Part268 (cell12367)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086529033502
  | 2 => 0.087492490349
  | 3 => 0.088457361196
  | 4 => 0.089425798046
  | 5 => 0.090400376087
  | 6 => 0.091384152819
  | 7 => 0.092380732086
  | 8 => 0.093394332936
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12367 12367 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12367 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12367

/-! Actual upper energy certificates on all 43 source endpoints at 12367. -/
namespace BstLean.Part269.N12367
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12367)
open BstLean.Part268 (cell12367)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12367 (gMinus 12367) (1 - (cell12367 i).lower) ≤ 1 ∧
    energyUpper 12367 (gMinus 12367) (BstLean.Part211.gPlus 12367)
      (finiteEnergy 12367 12367 0.011) (1 - (cell12367 i).lower) ≤
      (cell12367 i).energy := by
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
      have E := BstLean.Part269.S0.uniformEnergy10 (n := 12367) (by norm_num)
        (q := 1 - (cell12367 ⟨10,by decide⟩).lower)
        (by norm_num [cell12367]) (by norm_num [cell12367])
      exact ⟨E.1,E.2.trans (by norm_num [cell12367])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy11 (n := 12367) (by norm_num)
        (q := 1 - (cell12367 ⟨11,by decide⟩).lower)
        (by norm_num [cell12367]) (by norm_num [cell12367])
      exact ⟨E.1,E.2.trans (by norm_num [cell12367])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy12 (n := 12367) (by norm_num)
        (q := 1 - (cell12367 ⟨12,by decide⟩).lower)
        (by norm_num [cell12367]) (by norm_num [cell12367])
      exact ⟨E.1,E.2.trans (by norm_num [cell12367])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy13 (n := 12367) (by norm_num)
        (q := 1 - (cell12367 ⟨13,by decide⟩).lower)
        (by norm_num [cell12367]) (by norm_num [cell12367])
      exact ⟨E.1,E.2.trans (by norm_num [cell12367])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy14 (n := 12367) (by norm_num)
        (q := 1 - (cell12367 ⟨14,by decide⟩).lower)
        (by norm_num [cell12367]) (by norm_num [cell12367])
      exact ⟨E.1,E.2.trans (by norm_num [cell12367])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy15 (n := 12367) (by norm_num)
        (q := 1 - (cell12367 ⟨15,by decide⟩).lower)
        (by norm_num [cell12367]) (by norm_num [cell12367])
      exact ⟨E.1,E.2.trans (by norm_num [cell12367])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy16 (n := 12367) (by norm_num)
        (q := 1 - (cell12367 ⟨16,by decide⟩).lower)
        (by norm_num [cell12367]) (by norm_num [cell12367])
      exact ⟨E.1,E.2.trans (by norm_num [cell12367])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy17 (n := 12367) (by norm_num)
        (q := 1 - (cell12367 ⟨17,by decide⟩).lower)
        (by norm_num [cell12367]) (by norm_num [cell12367])
      exact ⟨E.1,E.2.trans (by norm_num [cell12367])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy18 (n := 12367) (by norm_num)
        (q := 1 - (cell12367 ⟨18,by decide⟩).lower)
        (by norm_num [cell12367]) (by norm_num [cell12367])
      exact ⟨E.1,E.2.trans (by norm_num [cell12367])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy19 (n := 12367) (by norm_num)
        (q := 1 - (cell12367 ⟨19,by decide⟩).lower)
        (by norm_num [cell12367]) (by norm_num [cell12367])
      exact ⟨E.1,E.2.trans (by norm_num [cell12367])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy20 (n := 12367) (by norm_num)
        (q := 1 - (cell12367 ⟨20,by decide⟩).lower)
        (by norm_num [cell12367]) (by norm_num [cell12367])
      exact ⟨E.1,E.2.trans (by norm_num [cell12367])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy21 (n := 12367) (by norm_num)
        (q := 1 - (cell12367 ⟨21,by decide⟩).lower)
        (by norm_num [cell12367]) (by norm_num [cell12367])
      exact ⟨E.1,E.2.trans (by norm_num [cell12367])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy22 (n := 12367) (by norm_num)
        (q := 1 - (cell12367 ⟨22,by decide⟩).lower)
        (by norm_num [cell12367]) (by norm_num [cell12367])
      exact ⟨E.1,E.2.trans (by norm_num [cell12367])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy23 (n := 12367) (by norm_num)
        (q := 1 - (cell12367 ⟨23,by decide⟩).lower)
        (by norm_num [cell12367]) (by norm_num [cell12367])
      exact ⟨E.1,E.2.trans (by norm_num [cell12367])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy24 (n := 12367) (by norm_num)
        (q := 1 - (cell12367 ⟨24,by decide⟩).lower)
        (by norm_num [cell12367]) (by norm_num [cell12367])
      exact ⟨E.1,E.2.trans (by norm_num [cell12367])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy25 (n := 12367) (by norm_num)
        (q := 1 - (cell12367 ⟨25,by decide⟩).lower)
        (by norm_num [cell12367]) (by norm_num [cell12367])
      exact ⟨E.1,E.2.trans (by norm_num [cell12367])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy26 (n := 12367) (by norm_num)
        (q := 1 - (cell12367 ⟨26,by decide⟩).lower)
        (by norm_num [cell12367]) (by norm_num [cell12367])
      exact ⟨E.1,E.2.trans (by norm_num [cell12367])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy27 (n := 12367) (by norm_num)
        (q := 1 - (cell12367 ⟨27,by decide⟩).lower)
        (by norm_num [cell12367]) (by norm_num [cell12367])
      exact ⟨E.1,E.2.trans (by norm_num [cell12367])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy28 (n := 12367) (by norm_num)
        (q := 1 - (cell12367 ⟨28,by decide⟩).lower)
        (by norm_num [cell12367]) (by norm_num [cell12367])
      exact ⟨E.1,E.2.trans (by norm_num [cell12367])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy29 (n := 12367) (by norm_num)
        (q := 1 - (cell12367 ⟨29,by decide⟩).lower)
        (by norm_num [cell12367]) (by norm_num [cell12367])
      exact ⟨E.1,E.2.trans (by norm_num [cell12367])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy30 (n := 12367) (by norm_num)
        (q := 1 - (cell12367 ⟨30,by decide⟩).lower)
        (by norm_num [cell12367]) (by norm_num [cell12367])
      exact ⟨E.1,E.2.trans (by norm_num [cell12367])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy31 (n := 12367) (by norm_num)
        (q := 1 - (cell12367 ⟨31,by decide⟩).lower)
        (by norm_num [cell12367]) (by norm_num [cell12367])
      exact ⟨E.1,E.2.trans (by norm_num [cell12367])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy32 (n := 12367) (by norm_num)
        (q := 1 - (cell12367 ⟨32,by decide⟩).lower)
        (by norm_num [cell12367]) (by norm_num [cell12367])
      exact ⟨E.1,E.2.trans (by norm_num [cell12367])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy33 (n := 12367) (by norm_num)
        (q := 1 - (cell12367 ⟨33,by decide⟩).lower)
        (by norm_num [cell12367]) (by norm_num [cell12367])
      exact ⟨E.1,E.2.trans (by norm_num [cell12367])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy34 (n := 12367) (by norm_num)
        (q := 1 - (cell12367 ⟨34,by decide⟩).lower)
        (by norm_num [cell12367]) (by norm_num [cell12367])
      exact ⟨E.1,E.2.trans (by norm_num [cell12367])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy35 (n := 12367) (by norm_num)
        (q := 1 - (cell12367 ⟨35,by decide⟩).lower)
        (by norm_num [cell12367]) (by norm_num [cell12367])
      exact ⟨E.1,E.2.trans (by norm_num [cell12367])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy36 (n := 12367) (by norm_num)
        (q := 1 - (cell12367 ⟨36,by decide⟩).lower)
        (by norm_num [cell12367]) (by norm_num [cell12367])
      exact ⟨E.1,E.2.trans (by norm_num [cell12367])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy37 (n := 12367) (by norm_num)
        (q := 1 - (cell12367 ⟨37,by decide⟩).lower)
        (by norm_num [cell12367]) (by norm_num [cell12367])
      exact ⟨E.1,E.2.trans (by norm_num [cell12367])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy38 (n := 12367) (by norm_num)
        (q := 1 - (cell12367 ⟨38,by decide⟩).lower)
        (by norm_num [cell12367]) (by norm_num [cell12367])
      exact ⟨E.1,E.2.trans (by norm_num [cell12367])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy39 (n := 12367) (by norm_num)
        (q := 1 - (cell12367 ⟨39,by decide⟩).lower)
        (by norm_num [cell12367]) (by norm_num [cell12367])
      exact ⟨E.1,E.2.trans (by norm_num [cell12367])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy40 (n := 12367) (by norm_num)
        (q := 1 - (cell12367 ⟨40,by decide⟩).lower)
        (by norm_num [cell12367]) (by norm_num [cell12367])
      exact ⟨E.1,E.2.trans (by norm_num [cell12367])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy41 (n := 12367) (by norm_num)
        (q := 1 - (cell12367 ⟨41,by decide⟩).lower)
        (by norm_num [cell12367]) (by norm_num [cell12367])
      exact ⟨E.1,E.2.trans (by norm_num [cell12367])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy42 (n := 12367) (by norm_num)
        (q := 1 - (cell12367 ⟨42,by decide⟩).lower)
        (by norm_num [cell12367]) (by norm_num [cell12367])
      exact ⟨E.1,E.2.trans (by norm_num [cell12367])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy43 (n := 12367) (by norm_num)
        (q := 1 - (cell12367 ⟨43,by decide⟩).lower)
        (by norm_num [cell12367]) (by norm_num [cell12367])
      exact ⟨E.1,E.2.trans (by norm_num [cell12367])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy44 (n := 12367) (by norm_num)
        (q := 1 - (cell12367 ⟨44,by decide⟩).lower)
        (by norm_num [cell12367]) (by norm_num [cell12367])
      exact ⟨E.1,E.2.trans (by norm_num [cell12367])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy45 (n := 12367) (by norm_num)
        (q := 1 - (cell12367 ⟨45,by decide⟩).lower)
        (by norm_num [cell12367]) (by norm_num [cell12367])
      exact ⟨E.1,E.2.trans (by norm_num [cell12367])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy46 (n := 12367) (by norm_num)
        (q := 1 - (cell12367 ⟨46,by decide⟩).lower)
        (by norm_num [cell12367]) (by norm_num [cell12367])
      exact ⟨E.1,E.2.trans (by norm_num [cell12367])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy47 (n := 12367) (by norm_num)
        (q := 1 - (cell12367 ⟨47,by decide⟩).lower)
        (by norm_num [cell12367]) (by norm_num [cell12367])
      exact ⟨E.1,E.2.trans (by norm_num [cell12367])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy48 (n := 12367) (by norm_num)
        (q := 1 - (cell12367 ⟨48,by decide⟩).lower)
        (by norm_num [cell12367]) (by norm_num [cell12367])
      exact ⟨E.1,E.2.trans (by norm_num [cell12367])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy49 (n := 12367) (by norm_num)
        (q := 1 - (cell12367 ⟨49,by decide⟩).lower)
        (by norm_num [cell12367]) (by norm_num [cell12367])
      exact ⟨E.1,E.2.trans (by norm_num [cell12367])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy50 (n := 12367) (by norm_num)
        (q := 1 - (cell12367 ⟨50,by decide⟩).lower)
        (by norm_num [cell12367]) (by norm_num [cell12367])
      exact ⟨E.1,E.2.trans (by norm_num [cell12367])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy51 (n := 12367) (by norm_num)
        (q := 1 - (cell12367 ⟨51,by decide⟩).lower)
        (by norm_num [cell12367]) (by norm_num [cell12367])
      exact ⟨E.1,E.2.trans (by norm_num [cell12367])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy52 (n := 12367) (by norm_num)
        (q := 1 - (cell12367 ⟨52,by decide⟩).lower)
        (by norm_num [cell12367]) (by norm_num [cell12367])
      exact ⟨E.1,E.2.trans (by norm_num [cell12367])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12367

/-! Source-cell containment and simple scalar guards at 12367. -/
namespace BstLean.Part269.N12367
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12367)
open BstLean.Part268 (cell12367)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12367 ⟨10,by decide⟩).lower ∧ (cell12367 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12367 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12367 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12367 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12367 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12367 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12367,cell12367,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12367 ⟨11,by decide⟩).lower ∧ (cell12367 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12367 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12367 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12367 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12367 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12367 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12367,cell12367,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12367 ⟨12,by decide⟩).lower ∧ (cell12367 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12367 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12367 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12367 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12367 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12367 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12367,cell12367,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12367 ⟨13,by decide⟩).lower ∧ (cell12367 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12367 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12367 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12367 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12367 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12367 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12367,cell12367,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12367 ⟨14,by decide⟩).lower ∧ (cell12367 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12367 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12367 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12367 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12367 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12367 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12367,cell12367,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12367 ⟨15,by decide⟩).lower ∧ (cell12367 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12367 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12367 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12367 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12367 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12367 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12367,cell12367,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12367 ⟨16,by decide⟩).lower ∧ (cell12367 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12367 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12367 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12367 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12367 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12367 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12367,cell12367,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12367 ⟨17,by decide⟩).lower ∧ (cell12367 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12367 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12367 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12367 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12367 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12367 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12367,cell12367,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12367 ⟨18,by decide⟩).lower ∧ (cell12367 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12367 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12367 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12367 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12367 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12367 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12367,cell12367,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12367 ⟨19,by decide⟩).lower ∧ (cell12367 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12367 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12367 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12367 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12367 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12367 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12367,cell12367,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12367 ⟨20,by decide⟩).lower ∧ (cell12367 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12367 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12367 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12367 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12367 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12367 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12367,cell12367,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12367 ⟨21,by decide⟩).lower ∧ (cell12367 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12367 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12367 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12367 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12367 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12367 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12367,cell12367,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12367 ⟨22,by decide⟩).lower ∧ (cell12367 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12367 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12367 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12367 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12367 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12367 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12367,cell12367,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12367 ⟨23,by decide⟩).lower ∧ (cell12367 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12367 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12367 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12367 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12367 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12367 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12367,cell12367,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12367 ⟨24,by decide⟩).lower ∧ (cell12367 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12367 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12367 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12367 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12367 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12367 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12367,cell12367,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12367 ⟨25,by decide⟩).lower ∧ (cell12367 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12367 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12367 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12367 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12367 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12367 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12367,cell12367,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12367 ⟨26,by decide⟩).lower ∧ (cell12367 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12367 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12367 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12367 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12367 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12367 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12367,cell12367,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12367 ⟨27,by decide⟩).lower ∧ (cell12367 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12367 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12367 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12367 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12367 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12367 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12367,cell12367,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12367 ⟨28,by decide⟩).lower ∧ (cell12367 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12367 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12367 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12367 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12367 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12367 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12367,cell12367,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12367 ⟨29,by decide⟩).lower ∧ (cell12367 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12367 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12367 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12367 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12367 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12367 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12367,cell12367,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12367 ⟨30,by decide⟩).lower ∧ (cell12367 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12367 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12367 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12367 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12367 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12367 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12367,cell12367,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12367 ⟨31,by decide⟩).lower ∧ (cell12367 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12367 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12367 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12367 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12367 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12367 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12367,cell12367,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12367 ⟨32,by decide⟩).lower ∧ (cell12367 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12367 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12367 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12367 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12367 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12367 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12367,cell12367,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12367 ⟨33,by decide⟩).lower ∧ (cell12367 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12367 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12367 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12367 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12367 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12367 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12367,cell12367,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12367 ⟨34,by decide⟩).lower ∧ (cell12367 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12367 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12367 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12367 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12367 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12367 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12367,cell12367,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12367 ⟨35,by decide⟩).lower ∧ (cell12367 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12367 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12367 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12367 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12367 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12367 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12367,cell12367,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12367 ⟨36,by decide⟩).lower ∧ (cell12367 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12367 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12367 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12367 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12367 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12367 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12367,cell12367,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12367 ⟨37,by decide⟩).lower ∧ (cell12367 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12367 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12367 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12367 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12367 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12367 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12367,cell12367,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12367 ⟨38,by decide⟩).lower ∧ (cell12367 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12367 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12367 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12367 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12367 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12367 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12367,cell12367,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12367 ⟨39,by decide⟩).lower ∧ (cell12367 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12367 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12367 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12367 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12367 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12367 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12367,cell12367,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12367 ⟨40,by decide⟩).lower ∧ (cell12367 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12367 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12367 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12367 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12367 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12367 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12367,cell12367,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12367 ⟨41,by decide⟩).lower ∧ (cell12367 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12367 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12367 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12367 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12367 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12367 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12367,cell12367,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12367 ⟨42,by decide⟩).lower ∧ (cell12367 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12367 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12367 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12367 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12367 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12367 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12367,cell12367,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12367 ⟨43,by decide⟩).lower ∧ (cell12367 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12367 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12367 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12367 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12367 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12367 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12367,cell12367,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12367 ⟨44,by decide⟩).lower ∧ (cell12367 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12367 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12367 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12367 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12367 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12367 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12367,cell12367,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12367 ⟨45,by decide⟩).lower ∧ (cell12367 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12367 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12367 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12367 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12367 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12367 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12367,cell12367,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12367 ⟨46,by decide⟩).lower ∧ (cell12367 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12367 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12367 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12367 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12367 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12367 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12367,cell12367,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12367 ⟨47,by decide⟩).lower ∧ (cell12367 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12367 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12367 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12367 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12367 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12367 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12367,cell12367,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12367 ⟨48,by decide⟩).lower ∧ (cell12367 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12367 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12367 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12367 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12367 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12367 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12367,cell12367,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12367 ⟨49,by decide⟩).lower ∧ (cell12367 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12367 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12367 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12367 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12367 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12367 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12367,cell12367,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12367 ⟨50,by decide⟩).lower ∧ (cell12367 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12367 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12367 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12367 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12367 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12367 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12367,cell12367,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12367 ⟨51,by decide⟩).lower ∧ (cell12367 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12367 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12367 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12367 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12367 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12367 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12367,cell12367,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12367 ⟨52,by decide⟩).lower ∧ (cell12367 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12367 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12367 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12367 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12367 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12367 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12367,cell12367,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12367 i).lower ∧
    (cell12367 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12367 i).upper ≤ (0.532 : ℝ) ∧
    (cell12367 i).centre ≤ (0.1 : ℝ) ∧ (cell12367 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12367 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12367 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12367

/-! The local source numeric instances at 12367 have no network premises. -/
namespace BstLean.Part269.N12367
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12367)
open BstLean.Part268 (cell12367)

noncomputable def sourceNumerics12367 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12367 (cell12367 i)
      scalarRow12367.M scalarRow12367.H scalarRow12367.xi := by
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
    energy_allowance := scalarRow12367.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12367]
    centre_nonneg := (scalarRow12367.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D0.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12367])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12367
/-! Actual 12368 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12368
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12368 ≤ (1.036290915329 : ℝ) := by
  have hr : (111.211510195662 : ℝ) ≤ √(12368 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.211510195662 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12368 12368 (11 / 1000) ≤
    (0.008595217582 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12368) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.211510195662 : ℝ) ≤ √(12368 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12368)
  have hdiv : K / √(12368 : ℝ) ≤ K / 111.211510195662 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.211510195662 ≤ (0.008595217582 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12368.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12368 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12368 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12368 := gPlus_lower 12368
end BstLean.Part269.N12368

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12368
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036290915328 : ℝ) ≤ wn 12368 := by
  have hn : √(12368 : ℝ) ≤ 111.211510195663 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12368 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.211510195663 ≤ 2 / √(12368 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000258762504 : ℝ) ≤ rhoBar 12368 BstLean.Part154.csC ∧
    rhoBar 12368 BstLean.Part154.csC ≤ 0.000258762905 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036290915328 : ℝ) / (1.295212 * 12368) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036290915329 : ℝ) / (1.29521 * 12368) := by gcongr
      _ ≤ (0.000258762905 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12368 BstLean.Part154.csC) ≤ 0.001035118579 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12368 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12368 BstLean.Part154.csC) (piBar (rhoBar 12368 BstLean.Part154.csC)) ≤ 0.000197645104 ∧
    cc1 (rhoBar 12368 BstLean.Part154.csC) (piBar (rhoBar 12368 BstLean.Part154.csC)) ≤ 0.000125762840 ∧
    cc2 (rhoBar 12368 BstLean.Part154.csC) ≤ 0.000073006229 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12368 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12368 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12368 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12368 BstLean.Part154.csC * nuR (rhoBar 12368 BstLean.Part154.csC)) ≤ 0.000517542550 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000258762905 : ℝ) * 0.001035118579 := by gcongr
      _ ≤ (0.000517542550 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12368 BstLean.Part154.csC) * nuR (rhoBar 12368 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001035118579 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12368 BstLean.Part154.csC) * rhoBar 12368 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000258762905 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000258762905 / 2 + 0.399 * 0.001035118579 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000197645104 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000517542550 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125762840 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000258762905 / 1.414213562 := by gcongr
      _ ≤ (0.000073006229 : ℝ) := by norm_num

end BstLean.Part269.N12368

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12368
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12368 BstLean.Part154.csC) (piBar (rhoBar 12368 BstLean.Part154.csC)) ≤ 1.68697E-7 := by
  have hr0 : 0 ≤ rhoBar 12368 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12368 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12368 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12368 BstLean.Part154.csC) (piBar (rhoBar 12368 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12368 BstLean.Part154.csC) (piBar (rhoBar 12368 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12368 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000197645104 : ℝ) ^ 2 + 0.000125762840 ^ 2 + 3 * 0.000073006229 ^ 2 +
        2 * 0.797885 * 0.000197645104 * 0.000125762840 + 2 * 0.000197645104 * 0.000073006229 +
        4 * 0.797885 * 0.000125762840 * 0.000073006229 := by gcongr
    _ ≤ (1.68697E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12368 BstLean.Part154.csC Θ ≤ 0.002702387956 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12368 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12368 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12368 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12368 BstLean.Part154.csC) (piBar (rhoBar 12368 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12368 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036290915329 * 1.68697E-7 / (0.000258762504 : ℝ) := by gcongr
    _ ≤ 0.002702387956 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12368 BstLean.Part154.csC Θ ≤ 0.002999835893 + 0.000682847799 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12368 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12368 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12368 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036290915329 : ℝ) * ((2 * Θ * 0.000258762905 +
        (6863 / 10000) * 0.000258762905 * 12368 * 0.001035118579) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002999835893 + 0.000682847799 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12368 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12368 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12368 0.011 Θ ∧ gammaRatio 12368 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12368 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036290915329 : ℝ) * 0.525 / ((1 - 0.011) * 12368) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12368 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12368 0.011 Θ) :=
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
    badAllowance 12368 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12368 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12368 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12368 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12368 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12368 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12368 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12368 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12368 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12368 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12368 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036290915329 : ℝ) * 12368 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12368 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004099835893 + 0.003385235755 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12368

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12368
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12368 BstLean.Part154.csC) (piBar (rhoBar 12368 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12368 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12368 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12368 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12368 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12368 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12368 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12368 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12368 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12368 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12368 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12368 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12368 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12368 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12368 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053191767375 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12368) ≤ 0.010738435069 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12368 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036290915329)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010738435069 + 2 * 0.737676 / 12368) := by gcongr
    _ ≤ (0.053191767375 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12368 12 ≤ 0.0015 := by
  exact BstLean.Part269.S0.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12368

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12368
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560488151237 : ℝ) ≤ plow 12368 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12368) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053383684665)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001418753677) : eMP 12368 0.011 xi bn ≤ 0.001220997931 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12368 : ℝ) * (1 - 0.011))) ≤ 0.000603643567 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001418753677 / (12368 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000603643567 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000603643567 : ℝ) + 3.141593 * 0.053383684665 / (12368 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001220997931 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053383684665)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001418753677) : PiBarMP 12368 12 0.011 xi bn ≤ 0.163424914951 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12368 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037666346744 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.598155499990 : ℝ) ≤ √((12368 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.211510195662 : ℝ) ≤ √(12368 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12368) ≤ 0.125278473769 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037666346744 + 0.053383684665 * 1.772454 / (2 * (110.598155499990 : ℝ))) * (1 + 0.001220997931) +
        8 / (12368 * 111.211510195662) + 0.125278473769 := by gcongr
    _ ≤ (0.163424914951 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053383684665)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001418753677) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284240863165) :
    parallelOracle 12368 0.011 xi bn cd ≤ 0.164445605843 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12368 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12368 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560488151237 : ℝ) ≤ plow 12368 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.211510195662 : ℝ) ≤ √(12368 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284240863165 : ℝ) / (2 * 0.560488151237 * 111.211510195662)) * 0.163424914951 +
        0.284240863165 ^ 2 / (2 * 0.560488151237 * 111.211510195662) := by gcongr
    _ ≤ (0.164445605843 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053383684665) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001418753677)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284240863165) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12368 12368 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560488151237 : ℝ) ≤ plow 12368 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.211510195662 : ℝ) ≤ √(12368 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12368 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12368 Θ 1.22 ≤ 0.011924129955 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.211510195662 := by gcongr <;> linarith
      _ ≤ (0.011924129955 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12368 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12368 12368 0.011 ≤ 0.008595217582 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12368 12368 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12368 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12368 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12368 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12368 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164445605843 + 0.011924129955 + (0.008595217582 : ℝ) *
        (1 + 2 * (0.284240863165 + 0.011924129955) / (0.560488151237 * 111.211510195662))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12368]

end BstLean.Part269.N12368

/-! The original eight local profiles supply actual 12368 moment certificates. -/
namespace BstLean.Part269.N12368
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12368 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12368 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12368 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053383684665 ∧
    0 ≤ bN 12368 BstLean.Part154.csC (groupTheta g) ∧ bN 12368 BstLean.Part154.csC (groupTheta g) ≤ 0.001418753677 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12368 12368 0.011
      (momentAllowance 12368 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12368 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12368 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12368 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12368 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12368 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231049095790 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12368 0.011
      (momentAllowance 12368 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12368 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12368
/-! The actual computed-centre upper energy formula at 12368. -/
namespace BstLean.Part269.N12368
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12368

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12368
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12368)
open BstLean.Part268 (cell12368)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086525686369
  | 2 => 0.087489071116
  | 3 => 0.088453857714
  | 4 => 0.089422195508
  | 5 => 0.090396656578
  | 6 => 0.091380294825
  | 7 => 0.092376709940
  | 8 => 0.093390116217
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12368 12368 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12368 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12368

/-! Actual upper energy certificates on all 43 source endpoints at 12368. -/
namespace BstLean.Part269.N12368
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12368)
open BstLean.Part268 (cell12368)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12368 (gMinus 12368) (1 - (cell12368 i).lower) ≤ 1 ∧
    energyUpper 12368 (gMinus 12368) (BstLean.Part211.gPlus 12368)
      (finiteEnergy 12368 12368 0.011) (1 - (cell12368 i).lower) ≤
      (cell12368 i).energy := by
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
      have E := BstLean.Part269.S0.uniformEnergy10 (n := 12368) (by norm_num)
        (q := 1 - (cell12368 ⟨10,by decide⟩).lower)
        (by norm_num [cell12368]) (by norm_num [cell12368])
      exact ⟨E.1,E.2.trans (by norm_num [cell12368])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy11 (n := 12368) (by norm_num)
        (q := 1 - (cell12368 ⟨11,by decide⟩).lower)
        (by norm_num [cell12368]) (by norm_num [cell12368])
      exact ⟨E.1,E.2.trans (by norm_num [cell12368])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy12 (n := 12368) (by norm_num)
        (q := 1 - (cell12368 ⟨12,by decide⟩).lower)
        (by norm_num [cell12368]) (by norm_num [cell12368])
      exact ⟨E.1,E.2.trans (by norm_num [cell12368])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy13 (n := 12368) (by norm_num)
        (q := 1 - (cell12368 ⟨13,by decide⟩).lower)
        (by norm_num [cell12368]) (by norm_num [cell12368])
      exact ⟨E.1,E.2.trans (by norm_num [cell12368])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy14 (n := 12368) (by norm_num)
        (q := 1 - (cell12368 ⟨14,by decide⟩).lower)
        (by norm_num [cell12368]) (by norm_num [cell12368])
      exact ⟨E.1,E.2.trans (by norm_num [cell12368])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy15 (n := 12368) (by norm_num)
        (q := 1 - (cell12368 ⟨15,by decide⟩).lower)
        (by norm_num [cell12368]) (by norm_num [cell12368])
      exact ⟨E.1,E.2.trans (by norm_num [cell12368])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy16 (n := 12368) (by norm_num)
        (q := 1 - (cell12368 ⟨16,by decide⟩).lower)
        (by norm_num [cell12368]) (by norm_num [cell12368])
      exact ⟨E.1,E.2.trans (by norm_num [cell12368])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy17 (n := 12368) (by norm_num)
        (q := 1 - (cell12368 ⟨17,by decide⟩).lower)
        (by norm_num [cell12368]) (by norm_num [cell12368])
      exact ⟨E.1,E.2.trans (by norm_num [cell12368])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy18 (n := 12368) (by norm_num)
        (q := 1 - (cell12368 ⟨18,by decide⟩).lower)
        (by norm_num [cell12368]) (by norm_num [cell12368])
      exact ⟨E.1,E.2.trans (by norm_num [cell12368])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy19 (n := 12368) (by norm_num)
        (q := 1 - (cell12368 ⟨19,by decide⟩).lower)
        (by norm_num [cell12368]) (by norm_num [cell12368])
      exact ⟨E.1,E.2.trans (by norm_num [cell12368])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy20 (n := 12368) (by norm_num)
        (q := 1 - (cell12368 ⟨20,by decide⟩).lower)
        (by norm_num [cell12368]) (by norm_num [cell12368])
      exact ⟨E.1,E.2.trans (by norm_num [cell12368])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy21 (n := 12368) (by norm_num)
        (q := 1 - (cell12368 ⟨21,by decide⟩).lower)
        (by norm_num [cell12368]) (by norm_num [cell12368])
      exact ⟨E.1,E.2.trans (by norm_num [cell12368])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy22 (n := 12368) (by norm_num)
        (q := 1 - (cell12368 ⟨22,by decide⟩).lower)
        (by norm_num [cell12368]) (by norm_num [cell12368])
      exact ⟨E.1,E.2.trans (by norm_num [cell12368])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy23 (n := 12368) (by norm_num)
        (q := 1 - (cell12368 ⟨23,by decide⟩).lower)
        (by norm_num [cell12368]) (by norm_num [cell12368])
      exact ⟨E.1,E.2.trans (by norm_num [cell12368])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy24 (n := 12368) (by norm_num)
        (q := 1 - (cell12368 ⟨24,by decide⟩).lower)
        (by norm_num [cell12368]) (by norm_num [cell12368])
      exact ⟨E.1,E.2.trans (by norm_num [cell12368])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy25 (n := 12368) (by norm_num)
        (q := 1 - (cell12368 ⟨25,by decide⟩).lower)
        (by norm_num [cell12368]) (by norm_num [cell12368])
      exact ⟨E.1,E.2.trans (by norm_num [cell12368])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy26 (n := 12368) (by norm_num)
        (q := 1 - (cell12368 ⟨26,by decide⟩).lower)
        (by norm_num [cell12368]) (by norm_num [cell12368])
      exact ⟨E.1,E.2.trans (by norm_num [cell12368])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy27 (n := 12368) (by norm_num)
        (q := 1 - (cell12368 ⟨27,by decide⟩).lower)
        (by norm_num [cell12368]) (by norm_num [cell12368])
      exact ⟨E.1,E.2.trans (by norm_num [cell12368])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy28 (n := 12368) (by norm_num)
        (q := 1 - (cell12368 ⟨28,by decide⟩).lower)
        (by norm_num [cell12368]) (by norm_num [cell12368])
      exact ⟨E.1,E.2.trans (by norm_num [cell12368])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy29 (n := 12368) (by norm_num)
        (q := 1 - (cell12368 ⟨29,by decide⟩).lower)
        (by norm_num [cell12368]) (by norm_num [cell12368])
      exact ⟨E.1,E.2.trans (by norm_num [cell12368])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy30 (n := 12368) (by norm_num)
        (q := 1 - (cell12368 ⟨30,by decide⟩).lower)
        (by norm_num [cell12368]) (by norm_num [cell12368])
      exact ⟨E.1,E.2.trans (by norm_num [cell12368])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy31 (n := 12368) (by norm_num)
        (q := 1 - (cell12368 ⟨31,by decide⟩).lower)
        (by norm_num [cell12368]) (by norm_num [cell12368])
      exact ⟨E.1,E.2.trans (by norm_num [cell12368])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy32 (n := 12368) (by norm_num)
        (q := 1 - (cell12368 ⟨32,by decide⟩).lower)
        (by norm_num [cell12368]) (by norm_num [cell12368])
      exact ⟨E.1,E.2.trans (by norm_num [cell12368])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy33 (n := 12368) (by norm_num)
        (q := 1 - (cell12368 ⟨33,by decide⟩).lower)
        (by norm_num [cell12368]) (by norm_num [cell12368])
      exact ⟨E.1,E.2.trans (by norm_num [cell12368])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy34 (n := 12368) (by norm_num)
        (q := 1 - (cell12368 ⟨34,by decide⟩).lower)
        (by norm_num [cell12368]) (by norm_num [cell12368])
      exact ⟨E.1,E.2.trans (by norm_num [cell12368])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy35 (n := 12368) (by norm_num)
        (q := 1 - (cell12368 ⟨35,by decide⟩).lower)
        (by norm_num [cell12368]) (by norm_num [cell12368])
      exact ⟨E.1,E.2.trans (by norm_num [cell12368])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy36 (n := 12368) (by norm_num)
        (q := 1 - (cell12368 ⟨36,by decide⟩).lower)
        (by norm_num [cell12368]) (by norm_num [cell12368])
      exact ⟨E.1,E.2.trans (by norm_num [cell12368])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy37 (n := 12368) (by norm_num)
        (q := 1 - (cell12368 ⟨37,by decide⟩).lower)
        (by norm_num [cell12368]) (by norm_num [cell12368])
      exact ⟨E.1,E.2.trans (by norm_num [cell12368])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy38 (n := 12368) (by norm_num)
        (q := 1 - (cell12368 ⟨38,by decide⟩).lower)
        (by norm_num [cell12368]) (by norm_num [cell12368])
      exact ⟨E.1,E.2.trans (by norm_num [cell12368])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy39 (n := 12368) (by norm_num)
        (q := 1 - (cell12368 ⟨39,by decide⟩).lower)
        (by norm_num [cell12368]) (by norm_num [cell12368])
      exact ⟨E.1,E.2.trans (by norm_num [cell12368])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy40 (n := 12368) (by norm_num)
        (q := 1 - (cell12368 ⟨40,by decide⟩).lower)
        (by norm_num [cell12368]) (by norm_num [cell12368])
      exact ⟨E.1,E.2.trans (by norm_num [cell12368])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy41 (n := 12368) (by norm_num)
        (q := 1 - (cell12368 ⟨41,by decide⟩).lower)
        (by norm_num [cell12368]) (by norm_num [cell12368])
      exact ⟨E.1,E.2.trans (by norm_num [cell12368])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy42 (n := 12368) (by norm_num)
        (q := 1 - (cell12368 ⟨42,by decide⟩).lower)
        (by norm_num [cell12368]) (by norm_num [cell12368])
      exact ⟨E.1,E.2.trans (by norm_num [cell12368])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy43 (n := 12368) (by norm_num)
        (q := 1 - (cell12368 ⟨43,by decide⟩).lower)
        (by norm_num [cell12368]) (by norm_num [cell12368])
      exact ⟨E.1,E.2.trans (by norm_num [cell12368])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy44 (n := 12368) (by norm_num)
        (q := 1 - (cell12368 ⟨44,by decide⟩).lower)
        (by norm_num [cell12368]) (by norm_num [cell12368])
      exact ⟨E.1,E.2.trans (by norm_num [cell12368])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy45 (n := 12368) (by norm_num)
        (q := 1 - (cell12368 ⟨45,by decide⟩).lower)
        (by norm_num [cell12368]) (by norm_num [cell12368])
      exact ⟨E.1,E.2.trans (by norm_num [cell12368])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy46 (n := 12368) (by norm_num)
        (q := 1 - (cell12368 ⟨46,by decide⟩).lower)
        (by norm_num [cell12368]) (by norm_num [cell12368])
      exact ⟨E.1,E.2.trans (by norm_num [cell12368])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy47 (n := 12368) (by norm_num)
        (q := 1 - (cell12368 ⟨47,by decide⟩).lower)
        (by norm_num [cell12368]) (by norm_num [cell12368])
      exact ⟨E.1,E.2.trans (by norm_num [cell12368])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy48 (n := 12368) (by norm_num)
        (q := 1 - (cell12368 ⟨48,by decide⟩).lower)
        (by norm_num [cell12368]) (by norm_num [cell12368])
      exact ⟨E.1,E.2.trans (by norm_num [cell12368])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy49 (n := 12368) (by norm_num)
        (q := 1 - (cell12368 ⟨49,by decide⟩).lower)
        (by norm_num [cell12368]) (by norm_num [cell12368])
      exact ⟨E.1,E.2.trans (by norm_num [cell12368])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy50 (n := 12368) (by norm_num)
        (q := 1 - (cell12368 ⟨50,by decide⟩).lower)
        (by norm_num [cell12368]) (by norm_num [cell12368])
      exact ⟨E.1,E.2.trans (by norm_num [cell12368])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy51 (n := 12368) (by norm_num)
        (q := 1 - (cell12368 ⟨51,by decide⟩).lower)
        (by norm_num [cell12368]) (by norm_num [cell12368])
      exact ⟨E.1,E.2.trans (by norm_num [cell12368])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy52 (n := 12368) (by norm_num)
        (q := 1 - (cell12368 ⟨52,by decide⟩).lower)
        (by norm_num [cell12368]) (by norm_num [cell12368])
      exact ⟨E.1,E.2.trans (by norm_num [cell12368])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12368

/-! Source-cell containment and simple scalar guards at 12368. -/
namespace BstLean.Part269.N12368
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12368)
open BstLean.Part268 (cell12368)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12368 ⟨10,by decide⟩).lower ∧ (cell12368 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12368 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12368 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12368 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12368 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12368 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12368,cell12368,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12368 ⟨11,by decide⟩).lower ∧ (cell12368 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12368 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12368 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12368 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12368 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12368 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12368,cell12368,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12368 ⟨12,by decide⟩).lower ∧ (cell12368 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12368 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12368 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12368 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12368 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12368 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12368,cell12368,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12368 ⟨13,by decide⟩).lower ∧ (cell12368 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12368 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12368 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12368 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12368 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12368 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12368,cell12368,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12368 ⟨14,by decide⟩).lower ∧ (cell12368 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12368 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12368 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12368 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12368 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12368 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12368,cell12368,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12368 ⟨15,by decide⟩).lower ∧ (cell12368 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12368 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12368 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12368 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12368 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12368 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12368,cell12368,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12368 ⟨16,by decide⟩).lower ∧ (cell12368 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12368 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12368 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12368 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12368 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12368 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12368,cell12368,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12368 ⟨17,by decide⟩).lower ∧ (cell12368 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12368 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12368 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12368 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12368 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12368 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12368,cell12368,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12368 ⟨18,by decide⟩).lower ∧ (cell12368 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12368 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12368 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12368 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12368 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12368 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12368,cell12368,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12368 ⟨19,by decide⟩).lower ∧ (cell12368 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12368 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12368 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12368 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12368 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12368 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12368,cell12368,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12368 ⟨20,by decide⟩).lower ∧ (cell12368 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12368 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12368 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12368 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12368 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12368 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12368,cell12368,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12368 ⟨21,by decide⟩).lower ∧ (cell12368 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12368 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12368 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12368 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12368 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12368 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12368,cell12368,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12368 ⟨22,by decide⟩).lower ∧ (cell12368 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12368 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12368 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12368 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12368 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12368 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12368,cell12368,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12368 ⟨23,by decide⟩).lower ∧ (cell12368 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12368 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12368 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12368 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12368 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12368 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12368,cell12368,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12368 ⟨24,by decide⟩).lower ∧ (cell12368 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12368 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12368 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12368 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12368 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12368 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12368,cell12368,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12368 ⟨25,by decide⟩).lower ∧ (cell12368 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12368 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12368 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12368 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12368 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12368 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12368,cell12368,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12368 ⟨26,by decide⟩).lower ∧ (cell12368 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12368 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12368 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12368 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12368 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12368 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12368,cell12368,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12368 ⟨27,by decide⟩).lower ∧ (cell12368 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12368 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12368 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12368 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12368 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12368 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12368,cell12368,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12368 ⟨28,by decide⟩).lower ∧ (cell12368 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12368 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12368 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12368 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12368 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12368 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12368,cell12368,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12368 ⟨29,by decide⟩).lower ∧ (cell12368 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12368 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12368 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12368 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12368 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12368 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12368,cell12368,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12368 ⟨30,by decide⟩).lower ∧ (cell12368 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12368 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12368 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12368 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12368 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12368 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12368,cell12368,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12368 ⟨31,by decide⟩).lower ∧ (cell12368 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12368 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12368 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12368 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12368 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12368 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12368,cell12368,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12368 ⟨32,by decide⟩).lower ∧ (cell12368 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12368 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12368 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12368 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12368 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12368 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12368,cell12368,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12368 ⟨33,by decide⟩).lower ∧ (cell12368 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12368 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12368 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12368 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12368 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12368 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12368,cell12368,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12368 ⟨34,by decide⟩).lower ∧ (cell12368 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12368 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12368 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12368 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12368 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12368 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12368,cell12368,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12368 ⟨35,by decide⟩).lower ∧ (cell12368 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12368 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12368 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12368 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12368 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12368 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12368,cell12368,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12368 ⟨36,by decide⟩).lower ∧ (cell12368 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12368 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12368 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12368 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12368 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12368 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12368,cell12368,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12368 ⟨37,by decide⟩).lower ∧ (cell12368 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12368 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12368 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12368 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12368 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12368 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12368,cell12368,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12368 ⟨38,by decide⟩).lower ∧ (cell12368 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12368 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12368 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12368 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12368 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12368 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12368,cell12368,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12368 ⟨39,by decide⟩).lower ∧ (cell12368 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12368 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12368 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12368 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12368 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12368 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12368,cell12368,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12368 ⟨40,by decide⟩).lower ∧ (cell12368 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12368 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12368 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12368 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12368 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12368 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12368,cell12368,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12368 ⟨41,by decide⟩).lower ∧ (cell12368 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12368 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12368 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12368 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12368 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12368 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12368,cell12368,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12368 ⟨42,by decide⟩).lower ∧ (cell12368 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12368 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12368 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12368 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12368 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12368 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12368,cell12368,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12368 ⟨43,by decide⟩).lower ∧ (cell12368 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12368 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12368 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12368 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12368 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12368 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12368,cell12368,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12368 ⟨44,by decide⟩).lower ∧ (cell12368 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12368 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12368 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12368 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12368 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12368 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12368,cell12368,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12368 ⟨45,by decide⟩).lower ∧ (cell12368 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12368 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12368 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12368 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12368 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12368 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12368,cell12368,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12368 ⟨46,by decide⟩).lower ∧ (cell12368 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12368 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12368 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12368 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12368 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12368 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12368,cell12368,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12368 ⟨47,by decide⟩).lower ∧ (cell12368 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12368 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12368 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12368 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12368 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12368 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12368,cell12368,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12368 ⟨48,by decide⟩).lower ∧ (cell12368 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12368 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12368 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12368 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12368 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12368 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12368,cell12368,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12368 ⟨49,by decide⟩).lower ∧ (cell12368 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12368 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12368 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12368 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12368 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12368 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12368,cell12368,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12368 ⟨50,by decide⟩).lower ∧ (cell12368 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12368 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12368 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12368 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12368 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12368 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12368,cell12368,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12368 ⟨51,by decide⟩).lower ∧ (cell12368 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12368 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12368 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12368 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12368 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12368 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12368,cell12368,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12368 ⟨52,by decide⟩).lower ∧ (cell12368 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12368 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12368 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12368 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12368 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12368 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12368,cell12368,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12368 i).lower ∧
    (cell12368 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12368 i).upper ≤ (0.532 : ℝ) ∧
    (cell12368 i).centre ≤ (0.1 : ℝ) ∧ (cell12368 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12368 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12368 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12368

/-! The local source numeric instances at 12368 have no network premises. -/
namespace BstLean.Part269.N12368
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12368)
open BstLean.Part268 (cell12368)

noncomputable def sourceNumerics12368 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12368 (cell12368 i)
      scalarRow12368.M scalarRow12368.H scalarRow12368.xi := by
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
    energy_allowance := scalarRow12368.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12368]
    centre_nonneg := (scalarRow12368.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D0.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12368])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12368
/-! Actual 12369 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12369
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12369 ≤ (1.036289435215 : ℝ) := by
  have hr : (111.216006042295 : ℝ) ≤ √(12369 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.216006042295 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12369 12369 (11 / 1000) ≤
    (0.008594870122 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12369) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.216006042295 : ℝ) ≤ √(12369 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12369)
  have hdiv : K / √(12369 : ℝ) ≤ K / 111.216006042295 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.216006042295 ≤ (0.008594870122 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12369.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12369 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12369 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12369 := gPlus_lower 12369
end BstLean.Part269.N12369

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12369
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036289435214 : ℝ) ≤ wn 12369 := by
  have hn : √(12369 : ℝ) ≤ 111.216006042296 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12369 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.216006042296 ≤ 2 / √(12369 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000258741214 : ℝ) ≤ rhoBar 12369 BstLean.Part154.csC ∧
    rhoBar 12369 BstLean.Part154.csC ≤ 0.000258741615 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036289435214 : ℝ) / (1.295212 * 12369) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036289435215 : ℝ) / (1.29521 * 12369) := by gcongr
      _ ≤ (0.000258741615 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12369 BstLean.Part154.csC) ≤ 0.001035033408 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12369 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12369 BstLean.Part154.csC) (piBar (rhoBar 12369 BstLean.Part154.csC)) ≤ 0.000197628841 ∧
    cc1 (rhoBar 12369 BstLean.Part154.csC) (piBar (rhoBar 12369 BstLean.Part154.csC)) ≤ 0.000125752492 ∧
    cc2 (rhoBar 12369 BstLean.Part154.csC) ≤ 0.000073000223 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12369 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12369 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12369 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12369 BstLean.Part154.csC * nuR (rhoBar 12369 BstLean.Part154.csC)) ≤ 0.000517499967 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000258741615 : ℝ) * 0.001035033408 := by gcongr
      _ ≤ (0.000517499967 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12369 BstLean.Part154.csC) * nuR (rhoBar 12369 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001035033408 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12369 BstLean.Part154.csC) * rhoBar 12369 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000258741615 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000258741615 / 2 + 0.399 * 0.001035033408 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000197628841 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000517499967 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125752492 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000258741615 / 1.414213562 := by gcongr
      _ ≤ (0.000073000223 : ℝ) := by norm_num

end BstLean.Part269.N12369

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12369
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12369 BstLean.Part154.csC) (piBar (rhoBar 12369 BstLean.Part154.csC)) ≤ 1.68669E-7 := by
  have hr0 : 0 ≤ rhoBar 12369 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12369 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12369 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12369 BstLean.Part154.csC) (piBar (rhoBar 12369 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12369 BstLean.Part154.csC) (piBar (rhoBar 12369 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12369 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000197628841 : ℝ) ^ 2 + 0.000125752492 ^ 2 + 3 * 0.000073000223 ^ 2 +
        2 * 0.797885 * 0.000197628841 * 0.000125752492 + 2 * 0.000197628841 * 0.000073000223 +
        4 * 0.797885 * 0.000125752492 * 0.000073000223 := by gcongr
    _ ≤ (1.68669E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12369 BstLean.Part154.csC Θ ≤ 0.002702157883 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12369 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12369 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12369 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12369 BstLean.Part154.csC) (piBar (rhoBar 12369 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12369 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036289435215 * 1.68669E-7 / (0.000258741214 : ℝ) := by gcongr
    _ ≤ 0.002702157883 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12369 BstLean.Part154.csC Θ ≤ 0.002999580492 + 0.000682790642 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12369 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12369 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12369 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036289435215 : ℝ) * ((2 * Θ * 0.000258741615 +
        (6863 / 10000) * 0.000258741615 * 12369 * 0.001035033408) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002999580492 + 0.000682790642 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12369 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12369 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12369 0.011 Θ ∧ gammaRatio 12369 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12369 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036289435215 : ℝ) * 0.525 / ((1 - 0.011) * 12369) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12369 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12369 0.011 Θ) :=
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
    badAllowance 12369 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12369 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12369 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12369 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12369 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12369 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12369 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12369 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12369 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12369 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12369 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036289435215 : ℝ) * 12369 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12369 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004099580492 + 0.003384948525 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12369

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12369
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12369 BstLean.Part154.csC) (piBar (rhoBar 12369 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12369 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12369 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12369 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12369 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12369 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12369 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12369 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12369 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12369 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12369 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12369 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12369 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12369 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12369 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053189593501 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12369) ≤ 0.010738000973 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12369 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036289435215)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010738000973 + 2 * 0.737676 / 12369) := by gcongr
    _ ≤ (0.053189593501 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12369 12 ≤ 0.0015 := by
  exact BstLean.Part269.S0.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12369

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12369
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560488198916 : ℝ) ≤ plow 12369 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12369) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053383278468)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001418632889) : eMP 12369 0.011 xi bn ≤ 0.001220896523 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12369 : ℝ) * (1 - 0.011))) ≤ 0.000603593469 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001418632889 / (12369 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000603593469 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000603593469 : ℝ) + 3.141593 * 0.053383278468 / (12369 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001220896523 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053383278468)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001418632889) : PiBarMP 12369 12 0.011 xi bn ≤ 0.163418220110 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12369 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037664743316 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.602626551090 : ℝ) ≤ √((12369 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.216006042295 : ℝ) ≤ √(12369 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12369) ≤ 0.125273409454 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037664743316 + 0.053383278468 * 1.772454 / (2 * (110.602626551090 : ℝ))) * (1 + 0.001220896523) +
        8 / (12369 * 111.216006042295) + 0.125273409454 := by gcongr
    _ ≤ (0.163418220110 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053383278468)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001418632889) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284237810262) :
    parallelOracle 12369 0.011 xi bn cd ≤ 0.164438836468 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12369 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12369 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560488198916 : ℝ) ≤ plow 12369 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.216006042295 : ℝ) ≤ √(12369 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284237810262 : ℝ) / (2 * 0.560488198916 * 111.216006042295)) * 0.163418220110 +
        0.284237810262 ^ 2 / (2 * 0.560488198916 * 111.216006042295) := by gcongr
    _ ≤ (0.164438836468 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053383278468) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001418632889)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284237810262) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12369 12369 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560488198916 : ℝ) ≤ plow 12369 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.216006042295 : ℝ) ≤ √(12369 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12369 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12369 Θ 1.22 ≤ 0.011923647928 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.216006042295 := by gcongr <;> linarith
      _ ≤ (0.011923647928 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12369 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12369 12369 0.011 ≤ 0.008594870122 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12369 12369 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12369 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12369 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12369 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12369 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164438836468 + 0.011923647928 + (0.008594870122 : ℝ) *
        (1 + 2 * (0.284237810262 + 0.011923647928) / (0.560488198916 * 111.216006042295))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12369]

end BstLean.Part269.N12369

/-! The original eight local profiles supply actual 12369 moment certificates. -/
namespace BstLean.Part269.N12369
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12369 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12369 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12369 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053383278468 ∧
    0 ≤ bN 12369 BstLean.Part154.csC (groupTheta g) ∧ bN 12369 BstLean.Part154.csC (groupTheta g) ≤ 0.001418632889 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12369 12369 0.011
      (momentAllowance 12369 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12369 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12369 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12369 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12369 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12369 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231048216761 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12369 0.011
      (momentAllowance 12369 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12369 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12369
/-! The actual computed-centre upper energy formula at 12369. -/
namespace BstLean.Part269.N12369
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12369

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12369
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12369)
open BstLean.Part268 (cell12369)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086522340776
  | 2 => 0.087485653490
  | 3 => 0.088450355925
  | 4 => 0.089418594766
  | 5 => 0.090392938993
  | 6 => 0.091376438907
  | 7 => 0.092372690054
  | 8 => 0.093385901978
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12369 12369 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12369 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12369

/-! Actual upper energy certificates on all 43 source endpoints at 12369. -/
namespace BstLean.Part269.N12369
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12369)
open BstLean.Part268 (cell12369)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12369 (gMinus 12369) (1 - (cell12369 i).lower) ≤ 1 ∧
    energyUpper 12369 (gMinus 12369) (BstLean.Part211.gPlus 12369)
      (finiteEnergy 12369 12369 0.011) (1 - (cell12369 i).lower) ≤
      (cell12369 i).energy := by
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
      have E := BstLean.Part269.S0.uniformEnergy10 (n := 12369) (by norm_num)
        (q := 1 - (cell12369 ⟨10,by decide⟩).lower)
        (by norm_num [cell12369]) (by norm_num [cell12369])
      exact ⟨E.1,E.2.trans (by norm_num [cell12369])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy11 (n := 12369) (by norm_num)
        (q := 1 - (cell12369 ⟨11,by decide⟩).lower)
        (by norm_num [cell12369]) (by norm_num [cell12369])
      exact ⟨E.1,E.2.trans (by norm_num [cell12369])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy12 (n := 12369) (by norm_num)
        (q := 1 - (cell12369 ⟨12,by decide⟩).lower)
        (by norm_num [cell12369]) (by norm_num [cell12369])
      exact ⟨E.1,E.2.trans (by norm_num [cell12369])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy13 (n := 12369) (by norm_num)
        (q := 1 - (cell12369 ⟨13,by decide⟩).lower)
        (by norm_num [cell12369]) (by norm_num [cell12369])
      exact ⟨E.1,E.2.trans (by norm_num [cell12369])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy14 (n := 12369) (by norm_num)
        (q := 1 - (cell12369 ⟨14,by decide⟩).lower)
        (by norm_num [cell12369]) (by norm_num [cell12369])
      exact ⟨E.1,E.2.trans (by norm_num [cell12369])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy15 (n := 12369) (by norm_num)
        (q := 1 - (cell12369 ⟨15,by decide⟩).lower)
        (by norm_num [cell12369]) (by norm_num [cell12369])
      exact ⟨E.1,E.2.trans (by norm_num [cell12369])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy16 (n := 12369) (by norm_num)
        (q := 1 - (cell12369 ⟨16,by decide⟩).lower)
        (by norm_num [cell12369]) (by norm_num [cell12369])
      exact ⟨E.1,E.2.trans (by norm_num [cell12369])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy17 (n := 12369) (by norm_num)
        (q := 1 - (cell12369 ⟨17,by decide⟩).lower)
        (by norm_num [cell12369]) (by norm_num [cell12369])
      exact ⟨E.1,E.2.trans (by norm_num [cell12369])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy18 (n := 12369) (by norm_num)
        (q := 1 - (cell12369 ⟨18,by decide⟩).lower)
        (by norm_num [cell12369]) (by norm_num [cell12369])
      exact ⟨E.1,E.2.trans (by norm_num [cell12369])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy19 (n := 12369) (by norm_num)
        (q := 1 - (cell12369 ⟨19,by decide⟩).lower)
        (by norm_num [cell12369]) (by norm_num [cell12369])
      exact ⟨E.1,E.2.trans (by norm_num [cell12369])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy20 (n := 12369) (by norm_num)
        (q := 1 - (cell12369 ⟨20,by decide⟩).lower)
        (by norm_num [cell12369]) (by norm_num [cell12369])
      exact ⟨E.1,E.2.trans (by norm_num [cell12369])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy21 (n := 12369) (by norm_num)
        (q := 1 - (cell12369 ⟨21,by decide⟩).lower)
        (by norm_num [cell12369]) (by norm_num [cell12369])
      exact ⟨E.1,E.2.trans (by norm_num [cell12369])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy22 (n := 12369) (by norm_num)
        (q := 1 - (cell12369 ⟨22,by decide⟩).lower)
        (by norm_num [cell12369]) (by norm_num [cell12369])
      exact ⟨E.1,E.2.trans (by norm_num [cell12369])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy23 (n := 12369) (by norm_num)
        (q := 1 - (cell12369 ⟨23,by decide⟩).lower)
        (by norm_num [cell12369]) (by norm_num [cell12369])
      exact ⟨E.1,E.2.trans (by norm_num [cell12369])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy24 (n := 12369) (by norm_num)
        (q := 1 - (cell12369 ⟨24,by decide⟩).lower)
        (by norm_num [cell12369]) (by norm_num [cell12369])
      exact ⟨E.1,E.2.trans (by norm_num [cell12369])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy25 (n := 12369) (by norm_num)
        (q := 1 - (cell12369 ⟨25,by decide⟩).lower)
        (by norm_num [cell12369]) (by norm_num [cell12369])
      exact ⟨E.1,E.2.trans (by norm_num [cell12369])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy26 (n := 12369) (by norm_num)
        (q := 1 - (cell12369 ⟨26,by decide⟩).lower)
        (by norm_num [cell12369]) (by norm_num [cell12369])
      exact ⟨E.1,E.2.trans (by norm_num [cell12369])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy27 (n := 12369) (by norm_num)
        (q := 1 - (cell12369 ⟨27,by decide⟩).lower)
        (by norm_num [cell12369]) (by norm_num [cell12369])
      exact ⟨E.1,E.2.trans (by norm_num [cell12369])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy28 (n := 12369) (by norm_num)
        (q := 1 - (cell12369 ⟨28,by decide⟩).lower)
        (by norm_num [cell12369]) (by norm_num [cell12369])
      exact ⟨E.1,E.2.trans (by norm_num [cell12369])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy29 (n := 12369) (by norm_num)
        (q := 1 - (cell12369 ⟨29,by decide⟩).lower)
        (by norm_num [cell12369]) (by norm_num [cell12369])
      exact ⟨E.1,E.2.trans (by norm_num [cell12369])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy30 (n := 12369) (by norm_num)
        (q := 1 - (cell12369 ⟨30,by decide⟩).lower)
        (by norm_num [cell12369]) (by norm_num [cell12369])
      exact ⟨E.1,E.2.trans (by norm_num [cell12369])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy31 (n := 12369) (by norm_num)
        (q := 1 - (cell12369 ⟨31,by decide⟩).lower)
        (by norm_num [cell12369]) (by norm_num [cell12369])
      exact ⟨E.1,E.2.trans (by norm_num [cell12369])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy32 (n := 12369) (by norm_num)
        (q := 1 - (cell12369 ⟨32,by decide⟩).lower)
        (by norm_num [cell12369]) (by norm_num [cell12369])
      exact ⟨E.1,E.2.trans (by norm_num [cell12369])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy33 (n := 12369) (by norm_num)
        (q := 1 - (cell12369 ⟨33,by decide⟩).lower)
        (by norm_num [cell12369]) (by norm_num [cell12369])
      exact ⟨E.1,E.2.trans (by norm_num [cell12369])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy34 (n := 12369) (by norm_num)
        (q := 1 - (cell12369 ⟨34,by decide⟩).lower)
        (by norm_num [cell12369]) (by norm_num [cell12369])
      exact ⟨E.1,E.2.trans (by norm_num [cell12369])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy35 (n := 12369) (by norm_num)
        (q := 1 - (cell12369 ⟨35,by decide⟩).lower)
        (by norm_num [cell12369]) (by norm_num [cell12369])
      exact ⟨E.1,E.2.trans (by norm_num [cell12369])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy36 (n := 12369) (by norm_num)
        (q := 1 - (cell12369 ⟨36,by decide⟩).lower)
        (by norm_num [cell12369]) (by norm_num [cell12369])
      exact ⟨E.1,E.2.trans (by norm_num [cell12369])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy37 (n := 12369) (by norm_num)
        (q := 1 - (cell12369 ⟨37,by decide⟩).lower)
        (by norm_num [cell12369]) (by norm_num [cell12369])
      exact ⟨E.1,E.2.trans (by norm_num [cell12369])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy38 (n := 12369) (by norm_num)
        (q := 1 - (cell12369 ⟨38,by decide⟩).lower)
        (by norm_num [cell12369]) (by norm_num [cell12369])
      exact ⟨E.1,E.2.trans (by norm_num [cell12369])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy39 (n := 12369) (by norm_num)
        (q := 1 - (cell12369 ⟨39,by decide⟩).lower)
        (by norm_num [cell12369]) (by norm_num [cell12369])
      exact ⟨E.1,E.2.trans (by norm_num [cell12369])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy40 (n := 12369) (by norm_num)
        (q := 1 - (cell12369 ⟨40,by decide⟩).lower)
        (by norm_num [cell12369]) (by norm_num [cell12369])
      exact ⟨E.1,E.2.trans (by norm_num [cell12369])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy41 (n := 12369) (by norm_num)
        (q := 1 - (cell12369 ⟨41,by decide⟩).lower)
        (by norm_num [cell12369]) (by norm_num [cell12369])
      exact ⟨E.1,E.2.trans (by norm_num [cell12369])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy42 (n := 12369) (by norm_num)
        (q := 1 - (cell12369 ⟨42,by decide⟩).lower)
        (by norm_num [cell12369]) (by norm_num [cell12369])
      exact ⟨E.1,E.2.trans (by norm_num [cell12369])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy43 (n := 12369) (by norm_num)
        (q := 1 - (cell12369 ⟨43,by decide⟩).lower)
        (by norm_num [cell12369]) (by norm_num [cell12369])
      exact ⟨E.1,E.2.trans (by norm_num [cell12369])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy44 (n := 12369) (by norm_num)
        (q := 1 - (cell12369 ⟨44,by decide⟩).lower)
        (by norm_num [cell12369]) (by norm_num [cell12369])
      exact ⟨E.1,E.2.trans (by norm_num [cell12369])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy45 (n := 12369) (by norm_num)
        (q := 1 - (cell12369 ⟨45,by decide⟩).lower)
        (by norm_num [cell12369]) (by norm_num [cell12369])
      exact ⟨E.1,E.2.trans (by norm_num [cell12369])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy46 (n := 12369) (by norm_num)
        (q := 1 - (cell12369 ⟨46,by decide⟩).lower)
        (by norm_num [cell12369]) (by norm_num [cell12369])
      exact ⟨E.1,E.2.trans (by norm_num [cell12369])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy47 (n := 12369) (by norm_num)
        (q := 1 - (cell12369 ⟨47,by decide⟩).lower)
        (by norm_num [cell12369]) (by norm_num [cell12369])
      exact ⟨E.1,E.2.trans (by norm_num [cell12369])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy48 (n := 12369) (by norm_num)
        (q := 1 - (cell12369 ⟨48,by decide⟩).lower)
        (by norm_num [cell12369]) (by norm_num [cell12369])
      exact ⟨E.1,E.2.trans (by norm_num [cell12369])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy49 (n := 12369) (by norm_num)
        (q := 1 - (cell12369 ⟨49,by decide⟩).lower)
        (by norm_num [cell12369]) (by norm_num [cell12369])
      exact ⟨E.1,E.2.trans (by norm_num [cell12369])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy50 (n := 12369) (by norm_num)
        (q := 1 - (cell12369 ⟨50,by decide⟩).lower)
        (by norm_num [cell12369]) (by norm_num [cell12369])
      exact ⟨E.1,E.2.trans (by norm_num [cell12369])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy51 (n := 12369) (by norm_num)
        (q := 1 - (cell12369 ⟨51,by decide⟩).lower)
        (by norm_num [cell12369]) (by norm_num [cell12369])
      exact ⟨E.1,E.2.trans (by norm_num [cell12369])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy52 (n := 12369) (by norm_num)
        (q := 1 - (cell12369 ⟨52,by decide⟩).lower)
        (by norm_num [cell12369]) (by norm_num [cell12369])
      exact ⟨E.1,E.2.trans (by norm_num [cell12369])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12369

/-! Source-cell containment and simple scalar guards at 12369. -/
namespace BstLean.Part269.N12369
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12369)
open BstLean.Part268 (cell12369)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12369 ⟨10,by decide⟩).lower ∧ (cell12369 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12369 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12369 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12369 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12369 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12369 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12369,cell12369,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12369 ⟨11,by decide⟩).lower ∧ (cell12369 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12369 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12369 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12369 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12369 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12369 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12369,cell12369,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12369 ⟨12,by decide⟩).lower ∧ (cell12369 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12369 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12369 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12369 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12369 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12369 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12369,cell12369,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12369 ⟨13,by decide⟩).lower ∧ (cell12369 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12369 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12369 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12369 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12369 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12369 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12369,cell12369,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12369 ⟨14,by decide⟩).lower ∧ (cell12369 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12369 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12369 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12369 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12369 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12369 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12369,cell12369,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12369 ⟨15,by decide⟩).lower ∧ (cell12369 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12369 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12369 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12369 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12369 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12369 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12369,cell12369,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12369 ⟨16,by decide⟩).lower ∧ (cell12369 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12369 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12369 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12369 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12369 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12369 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12369,cell12369,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12369 ⟨17,by decide⟩).lower ∧ (cell12369 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12369 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12369 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12369 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12369 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12369 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12369,cell12369,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12369 ⟨18,by decide⟩).lower ∧ (cell12369 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12369 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12369 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12369 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12369 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12369 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12369,cell12369,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12369 ⟨19,by decide⟩).lower ∧ (cell12369 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12369 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12369 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12369 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12369 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12369 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12369,cell12369,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12369 ⟨20,by decide⟩).lower ∧ (cell12369 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12369 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12369 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12369 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12369 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12369 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12369,cell12369,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12369 ⟨21,by decide⟩).lower ∧ (cell12369 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12369 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12369 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12369 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12369 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12369 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12369,cell12369,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12369 ⟨22,by decide⟩).lower ∧ (cell12369 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12369 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12369 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12369 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12369 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12369 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12369,cell12369,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12369 ⟨23,by decide⟩).lower ∧ (cell12369 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12369 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12369 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12369 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12369 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12369 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12369,cell12369,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12369 ⟨24,by decide⟩).lower ∧ (cell12369 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12369 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12369 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12369 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12369 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12369 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12369,cell12369,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12369 ⟨25,by decide⟩).lower ∧ (cell12369 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12369 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12369 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12369 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12369 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12369 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12369,cell12369,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12369 ⟨26,by decide⟩).lower ∧ (cell12369 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12369 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12369 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12369 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12369 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12369 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12369,cell12369,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12369 ⟨27,by decide⟩).lower ∧ (cell12369 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12369 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12369 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12369 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12369 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12369 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12369,cell12369,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12369 ⟨28,by decide⟩).lower ∧ (cell12369 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12369 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12369 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12369 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12369 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12369 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12369,cell12369,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12369 ⟨29,by decide⟩).lower ∧ (cell12369 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12369 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12369 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12369 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12369 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12369 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12369,cell12369,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12369 ⟨30,by decide⟩).lower ∧ (cell12369 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12369 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12369 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12369 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12369 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12369 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12369,cell12369,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12369 ⟨31,by decide⟩).lower ∧ (cell12369 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12369 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12369 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12369 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12369 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12369 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12369,cell12369,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12369 ⟨32,by decide⟩).lower ∧ (cell12369 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12369 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12369 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12369 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12369 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12369 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12369,cell12369,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12369 ⟨33,by decide⟩).lower ∧ (cell12369 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12369 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12369 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12369 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12369 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12369 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12369,cell12369,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12369 ⟨34,by decide⟩).lower ∧ (cell12369 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12369 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12369 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12369 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12369 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12369 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12369,cell12369,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12369 ⟨35,by decide⟩).lower ∧ (cell12369 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12369 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12369 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12369 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12369 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12369 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12369,cell12369,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12369 ⟨36,by decide⟩).lower ∧ (cell12369 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12369 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12369 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12369 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12369 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12369 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12369,cell12369,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12369 ⟨37,by decide⟩).lower ∧ (cell12369 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12369 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12369 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12369 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12369 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12369 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12369,cell12369,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12369 ⟨38,by decide⟩).lower ∧ (cell12369 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12369 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12369 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12369 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12369 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12369 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12369,cell12369,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12369 ⟨39,by decide⟩).lower ∧ (cell12369 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12369 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12369 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12369 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12369 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12369 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12369,cell12369,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12369 ⟨40,by decide⟩).lower ∧ (cell12369 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12369 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12369 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12369 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12369 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12369 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12369,cell12369,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12369 ⟨41,by decide⟩).lower ∧ (cell12369 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12369 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12369 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12369 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12369 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12369 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12369,cell12369,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12369 ⟨42,by decide⟩).lower ∧ (cell12369 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12369 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12369 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12369 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12369 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12369 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12369,cell12369,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12369 ⟨43,by decide⟩).lower ∧ (cell12369 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12369 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12369 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12369 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12369 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12369 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12369,cell12369,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12369 ⟨44,by decide⟩).lower ∧ (cell12369 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12369 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12369 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12369 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12369 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12369 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12369,cell12369,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12369 ⟨45,by decide⟩).lower ∧ (cell12369 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12369 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12369 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12369 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12369 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12369 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12369,cell12369,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12369 ⟨46,by decide⟩).lower ∧ (cell12369 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12369 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12369 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12369 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12369 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12369 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12369,cell12369,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12369 ⟨47,by decide⟩).lower ∧ (cell12369 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12369 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12369 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12369 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12369 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12369 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12369,cell12369,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12369 ⟨48,by decide⟩).lower ∧ (cell12369 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12369 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12369 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12369 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12369 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12369 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12369,cell12369,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12369 ⟨49,by decide⟩).lower ∧ (cell12369 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12369 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12369 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12369 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12369 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12369 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12369,cell12369,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12369 ⟨50,by decide⟩).lower ∧ (cell12369 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12369 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12369 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12369 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12369 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12369 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12369,cell12369,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12369 ⟨51,by decide⟩).lower ∧ (cell12369 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12369 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12369 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12369 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12369 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12369 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12369,cell12369,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12369 ⟨52,by decide⟩).lower ∧ (cell12369 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12369 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12369 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12369 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12369 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12369 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12369,cell12369,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12369 i).lower ∧
    (cell12369 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12369 i).upper ≤ (0.532 : ℝ) ∧
    (cell12369 i).centre ≤ (0.1 : ℝ) ∧ (cell12369 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12369 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12369 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12369

/-! The local source numeric instances at 12369 have no network premises. -/
namespace BstLean.Part269.N12369
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12369)
open BstLean.Part268 (cell12369)

noncomputable def sourceNumerics12369 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12369 (cell12369 i)
      scalarRow12369.M scalarRow12369.H scalarRow12369.xi := by
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
    energy_allowance := scalarRow12369.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12369]
    centre_nonneg := (scalarRow12369.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D0.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12369])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12369
/-! Actual 12370 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12370
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12370 ≤ (1.036287955282 : ℝ) := by
  have hr : (111.220501707194 : ℝ) ≤ √(12370 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.220501707194 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12370 12370 (11 / 1000) ≤
    (0.008594522705 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12370) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.220501707194 : ℝ) ≤ √(12370 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12370)
  have hdiv : K / √(12370 : ℝ) ≤ K / 111.220501707194 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.220501707194 ≤ (0.008594522705 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12370.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12370 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12370 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12370 := gPlus_lower 12370
end BstLean.Part269.N12370

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12370
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036287955281 : ℝ) ≤ wn 12370 := by
  have hn : √(12370 : ℝ) ≤ 111.220501707195 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12370 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.220501707195 ≤ 2 / √(12370 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000258719928 : ℝ) ≤ rhoBar 12370 BstLean.Part154.csC ∧
    rhoBar 12370 BstLean.Part154.csC ≤ 0.000258720329 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036287955281 : ℝ) / (1.295212 * 12370) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036287955282 : ℝ) / (1.29521 * 12370) := by gcongr
      _ ≤ (0.000258720329 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12370 BstLean.Part154.csC) ≤ 0.001034948253 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12370 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12370 BstLean.Part154.csC) (piBar (rhoBar 12370 BstLean.Part154.csC)) ≤ 0.000197612582 ∧
    cc1 (rhoBar 12370 BstLean.Part154.csC) (piBar (rhoBar 12370 BstLean.Part154.csC)) ≤ 0.000125742147 ∧
    cc2 (rhoBar 12370 BstLean.Part154.csC) ≤ 0.000072994217 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12370 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12370 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12370 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12370 BstLean.Part154.csC * nuR (rhoBar 12370 BstLean.Part154.csC)) ≤ 0.000517457392 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000258720329 : ℝ) * 0.001034948253 := by gcongr
      _ ≤ (0.000517457392 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12370 BstLean.Part154.csC) * nuR (rhoBar 12370 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001034948253 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12370 BstLean.Part154.csC) * rhoBar 12370 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000258720329 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000258720329 / 2 + 0.399 * 0.001034948253 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000197612582 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000517457392 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125742147 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000258720329 / 1.414213562 := by gcongr
      _ ≤ (0.000072994217 : ℝ) := by norm_num

end BstLean.Part269.N12370

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12370
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12370 BstLean.Part154.csC) (piBar (rhoBar 12370 BstLean.Part154.csC)) ≤ 1.68641E-7 := by
  have hr0 : 0 ≤ rhoBar 12370 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12370 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12370 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12370 BstLean.Part154.csC) (piBar (rhoBar 12370 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12370 BstLean.Part154.csC) (piBar (rhoBar 12370 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12370 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000197612582 : ℝ) ^ 2 + 0.000125742147 ^ 2 + 3 * 0.000072994217 ^ 2 +
        2 * 0.797885 * 0.000197612582 * 0.000125742147 + 2 * 0.000197612582 * 0.000072994217 +
        4 * 0.797885 * 0.000125742147 * 0.000072994217 := by gcongr
    _ ≤ (1.68641E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12370 BstLean.Part154.csC Θ ≤ 0.002701927732 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12370 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12370 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12370 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12370 BstLean.Part154.csC) (piBar (rhoBar 12370 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12370 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036287955282 * 1.68641E-7 / (0.000258719928 : ℝ) := by gcongr
    _ ≤ 0.002701927732 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12370 BstLean.Part154.csC Θ ≤ 0.002999325146 + 0.000682733495 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12370 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12370 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12370 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036287955282 : ℝ) * ((2 * Θ * 0.000258720329 +
        (6863 / 10000) * 0.000258720329 * 12370 * 0.001034948253) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002999325146 + 0.000682733495 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12370 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12370 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12370 0.011 Θ ∧ gammaRatio 12370 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12370 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036287955282 : ℝ) * 0.525 / ((1 - 0.011) * 12370) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12370 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12370 0.011 Θ) :=
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
    badAllowance 12370 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12370 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12370 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12370 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12370 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12370 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12370 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12370 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12370 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12370 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12370 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036287955282 : ℝ) * 12370 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12370 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004099325146 + 0.003384661227 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12370

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12370
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12370 BstLean.Part154.csC) (piBar (rhoBar 12370 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12370 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12370 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12370 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12370 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12370 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12370 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12370 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12370 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12370 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12370 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12370 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12370 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12370 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12370 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053187419895 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12370) ≤ 0.010737566930 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12370 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036287955282)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010737566930 + 2 * 0.737676 / 12370) := by gcongr
    _ ≤ (0.053187419895 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12370 12 ≤ 0.0015 := by
  exact BstLean.Part269.S0.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12370

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12370
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560488246588 : ℝ) ≤ plow 12370 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12370) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053382872291)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001418512060) : eMP 12370 0.011 xi bn ≤ 0.001220795106 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12370 : ℝ) * (1 - 0.011))) ≤ 0.000603543367 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001418512060 / (12370 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000603543367 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000603543367 : ℝ) + 3.141593 * 0.053382872291 / (12370 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001220795106 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053382872291)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001418512060) : PiBarMP 12370 12 0.011 xi bn ≤ 0.163411525273 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12370 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037663139275 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.607097421458 : ℝ) ≤ √((12370 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.220501707194 : ℝ) ≤ √(12370 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12370) ≤ 0.125268345754 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037663139275 + 0.053382872291 * 1.772454 / (2 * (110.607097421458 : ℝ))) * (1 + 0.001220795106) +
        8 / (12370 * 111.220501707194) + 0.125268345754 := by gcongr
    _ ≤ (0.163411525273 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053382872291)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001418512060) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284234757666) :
    parallelOracle 12370 0.011 xi bn cd ≤ 0.164432067107 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12370 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12370 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560488246588 : ℝ) ≤ plow 12370 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.220501707194 : ℝ) ≤ √(12370 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284234757666 : ℝ) / (2 * 0.560488246588 * 111.220501707194)) * 0.163411525273 +
        0.284234757666 ^ 2 / (2 * 0.560488246588 * 111.220501707194) := by gcongr
    _ ≤ (0.164432067107 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053382872291) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001418512060)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284234757666) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12370 12370 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560488246588 : ℝ) ≤ plow 12370 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.220501707194 : ℝ) ≤ √(12370 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12370 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12370 Θ 1.22 ≤ 0.011923165960 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.220501707194 := by gcongr <;> linarith
      _ ≤ (0.011923165960 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12370 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12370 12370 0.011 ≤ 0.008594522705 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12370 12370 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12370 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12370 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12370 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12370 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164432067107 + 0.011923165960 + (0.008594522705 : ℝ) *
        (1 + 2 * (0.284234757666 + 0.011923165960) / (0.560488246588 * 111.220501707194))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12370]

end BstLean.Part269.N12370

/-! The original eight local profiles supply actual 12370 moment certificates. -/
namespace BstLean.Part269.N12370
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12370 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12370 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12370 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053382872291 ∧
    0 ≤ bN 12370 BstLean.Part154.csC (groupTheta g) ∧ bN 12370 BstLean.Part154.csC (groupTheta g) ≤ 0.001418512060 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12370 12370 0.011
      (momentAllowance 12370 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12370 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12370 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12370 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12370 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12370 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231047337771 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12370 0.011
      (momentAllowance 12370 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12370 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12370
/-! The actual computed-centre upper energy formula at 12370. -/
namespace BstLean.Part269.N12370
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12370

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12370
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12370)
open BstLean.Part268 (cell12370)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086518996720
  | 2 => 0.087482237471
  | 3 => 0.088446855827
  | 4 => 0.089414995819
  | 5 => 0.090389223328
  | 6 => 0.091372585062
  | 7 => 0.092368672426
  | 8 => 0.093381690217
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12370 12370 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12370 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12370

/-! Actual upper energy certificates on all 43 source endpoints at 12370. -/
namespace BstLean.Part269.N12370
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12370)
open BstLean.Part268 (cell12370)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12370 (gMinus 12370) (1 - (cell12370 i).lower) ≤ 1 ∧
    energyUpper 12370 (gMinus 12370) (BstLean.Part211.gPlus 12370)
      (finiteEnergy 12370 12370 0.011) (1 - (cell12370 i).lower) ≤
      (cell12370 i).energy := by
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
      have E := BstLean.Part269.S0.uniformEnergy10 (n := 12370) (by norm_num)
        (q := 1 - (cell12370 ⟨10,by decide⟩).lower)
        (by norm_num [cell12370]) (by norm_num [cell12370])
      exact ⟨E.1,E.2.trans (by norm_num [cell12370])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy11 (n := 12370) (by norm_num)
        (q := 1 - (cell12370 ⟨11,by decide⟩).lower)
        (by norm_num [cell12370]) (by norm_num [cell12370])
      exact ⟨E.1,E.2.trans (by norm_num [cell12370])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy12 (n := 12370) (by norm_num)
        (q := 1 - (cell12370 ⟨12,by decide⟩).lower)
        (by norm_num [cell12370]) (by norm_num [cell12370])
      exact ⟨E.1,E.2.trans (by norm_num [cell12370])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy13 (n := 12370) (by norm_num)
        (q := 1 - (cell12370 ⟨13,by decide⟩).lower)
        (by norm_num [cell12370]) (by norm_num [cell12370])
      exact ⟨E.1,E.2.trans (by norm_num [cell12370])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy14 (n := 12370) (by norm_num)
        (q := 1 - (cell12370 ⟨14,by decide⟩).lower)
        (by norm_num [cell12370]) (by norm_num [cell12370])
      exact ⟨E.1,E.2.trans (by norm_num [cell12370])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy15 (n := 12370) (by norm_num)
        (q := 1 - (cell12370 ⟨15,by decide⟩).lower)
        (by norm_num [cell12370]) (by norm_num [cell12370])
      exact ⟨E.1,E.2.trans (by norm_num [cell12370])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy16 (n := 12370) (by norm_num)
        (q := 1 - (cell12370 ⟨16,by decide⟩).lower)
        (by norm_num [cell12370]) (by norm_num [cell12370])
      exact ⟨E.1,E.2.trans (by norm_num [cell12370])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy17 (n := 12370) (by norm_num)
        (q := 1 - (cell12370 ⟨17,by decide⟩).lower)
        (by norm_num [cell12370]) (by norm_num [cell12370])
      exact ⟨E.1,E.2.trans (by norm_num [cell12370])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy18 (n := 12370) (by norm_num)
        (q := 1 - (cell12370 ⟨18,by decide⟩).lower)
        (by norm_num [cell12370]) (by norm_num [cell12370])
      exact ⟨E.1,E.2.trans (by norm_num [cell12370])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy19 (n := 12370) (by norm_num)
        (q := 1 - (cell12370 ⟨19,by decide⟩).lower)
        (by norm_num [cell12370]) (by norm_num [cell12370])
      exact ⟨E.1,E.2.trans (by norm_num [cell12370])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy20 (n := 12370) (by norm_num)
        (q := 1 - (cell12370 ⟨20,by decide⟩).lower)
        (by norm_num [cell12370]) (by norm_num [cell12370])
      exact ⟨E.1,E.2.trans (by norm_num [cell12370])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy21 (n := 12370) (by norm_num)
        (q := 1 - (cell12370 ⟨21,by decide⟩).lower)
        (by norm_num [cell12370]) (by norm_num [cell12370])
      exact ⟨E.1,E.2.trans (by norm_num [cell12370])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy22 (n := 12370) (by norm_num)
        (q := 1 - (cell12370 ⟨22,by decide⟩).lower)
        (by norm_num [cell12370]) (by norm_num [cell12370])
      exact ⟨E.1,E.2.trans (by norm_num [cell12370])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy23 (n := 12370) (by norm_num)
        (q := 1 - (cell12370 ⟨23,by decide⟩).lower)
        (by norm_num [cell12370]) (by norm_num [cell12370])
      exact ⟨E.1,E.2.trans (by norm_num [cell12370])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy24 (n := 12370) (by norm_num)
        (q := 1 - (cell12370 ⟨24,by decide⟩).lower)
        (by norm_num [cell12370]) (by norm_num [cell12370])
      exact ⟨E.1,E.2.trans (by norm_num [cell12370])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy25 (n := 12370) (by norm_num)
        (q := 1 - (cell12370 ⟨25,by decide⟩).lower)
        (by norm_num [cell12370]) (by norm_num [cell12370])
      exact ⟨E.1,E.2.trans (by norm_num [cell12370])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy26 (n := 12370) (by norm_num)
        (q := 1 - (cell12370 ⟨26,by decide⟩).lower)
        (by norm_num [cell12370]) (by norm_num [cell12370])
      exact ⟨E.1,E.2.trans (by norm_num [cell12370])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy27 (n := 12370) (by norm_num)
        (q := 1 - (cell12370 ⟨27,by decide⟩).lower)
        (by norm_num [cell12370]) (by norm_num [cell12370])
      exact ⟨E.1,E.2.trans (by norm_num [cell12370])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy28 (n := 12370) (by norm_num)
        (q := 1 - (cell12370 ⟨28,by decide⟩).lower)
        (by norm_num [cell12370]) (by norm_num [cell12370])
      exact ⟨E.1,E.2.trans (by norm_num [cell12370])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy29 (n := 12370) (by norm_num)
        (q := 1 - (cell12370 ⟨29,by decide⟩).lower)
        (by norm_num [cell12370]) (by norm_num [cell12370])
      exact ⟨E.1,E.2.trans (by norm_num [cell12370])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy30 (n := 12370) (by norm_num)
        (q := 1 - (cell12370 ⟨30,by decide⟩).lower)
        (by norm_num [cell12370]) (by norm_num [cell12370])
      exact ⟨E.1,E.2.trans (by norm_num [cell12370])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy31 (n := 12370) (by norm_num)
        (q := 1 - (cell12370 ⟨31,by decide⟩).lower)
        (by norm_num [cell12370]) (by norm_num [cell12370])
      exact ⟨E.1,E.2.trans (by norm_num [cell12370])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy32 (n := 12370) (by norm_num)
        (q := 1 - (cell12370 ⟨32,by decide⟩).lower)
        (by norm_num [cell12370]) (by norm_num [cell12370])
      exact ⟨E.1,E.2.trans (by norm_num [cell12370])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy33 (n := 12370) (by norm_num)
        (q := 1 - (cell12370 ⟨33,by decide⟩).lower)
        (by norm_num [cell12370]) (by norm_num [cell12370])
      exact ⟨E.1,E.2.trans (by norm_num [cell12370])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy34 (n := 12370) (by norm_num)
        (q := 1 - (cell12370 ⟨34,by decide⟩).lower)
        (by norm_num [cell12370]) (by norm_num [cell12370])
      exact ⟨E.1,E.2.trans (by norm_num [cell12370])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy35 (n := 12370) (by norm_num)
        (q := 1 - (cell12370 ⟨35,by decide⟩).lower)
        (by norm_num [cell12370]) (by norm_num [cell12370])
      exact ⟨E.1,E.2.trans (by norm_num [cell12370])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy36 (n := 12370) (by norm_num)
        (q := 1 - (cell12370 ⟨36,by decide⟩).lower)
        (by norm_num [cell12370]) (by norm_num [cell12370])
      exact ⟨E.1,E.2.trans (by norm_num [cell12370])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy37 (n := 12370) (by norm_num)
        (q := 1 - (cell12370 ⟨37,by decide⟩).lower)
        (by norm_num [cell12370]) (by norm_num [cell12370])
      exact ⟨E.1,E.2.trans (by norm_num [cell12370])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy38 (n := 12370) (by norm_num)
        (q := 1 - (cell12370 ⟨38,by decide⟩).lower)
        (by norm_num [cell12370]) (by norm_num [cell12370])
      exact ⟨E.1,E.2.trans (by norm_num [cell12370])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy39 (n := 12370) (by norm_num)
        (q := 1 - (cell12370 ⟨39,by decide⟩).lower)
        (by norm_num [cell12370]) (by norm_num [cell12370])
      exact ⟨E.1,E.2.trans (by norm_num [cell12370])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy40 (n := 12370) (by norm_num)
        (q := 1 - (cell12370 ⟨40,by decide⟩).lower)
        (by norm_num [cell12370]) (by norm_num [cell12370])
      exact ⟨E.1,E.2.trans (by norm_num [cell12370])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy41 (n := 12370) (by norm_num)
        (q := 1 - (cell12370 ⟨41,by decide⟩).lower)
        (by norm_num [cell12370]) (by norm_num [cell12370])
      exact ⟨E.1,E.2.trans (by norm_num [cell12370])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy42 (n := 12370) (by norm_num)
        (q := 1 - (cell12370 ⟨42,by decide⟩).lower)
        (by norm_num [cell12370]) (by norm_num [cell12370])
      exact ⟨E.1,E.2.trans (by norm_num [cell12370])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy43 (n := 12370) (by norm_num)
        (q := 1 - (cell12370 ⟨43,by decide⟩).lower)
        (by norm_num [cell12370]) (by norm_num [cell12370])
      exact ⟨E.1,E.2.trans (by norm_num [cell12370])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy44 (n := 12370) (by norm_num)
        (q := 1 - (cell12370 ⟨44,by decide⟩).lower)
        (by norm_num [cell12370]) (by norm_num [cell12370])
      exact ⟨E.1,E.2.trans (by norm_num [cell12370])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy45 (n := 12370) (by norm_num)
        (q := 1 - (cell12370 ⟨45,by decide⟩).lower)
        (by norm_num [cell12370]) (by norm_num [cell12370])
      exact ⟨E.1,E.2.trans (by norm_num [cell12370])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy46 (n := 12370) (by norm_num)
        (q := 1 - (cell12370 ⟨46,by decide⟩).lower)
        (by norm_num [cell12370]) (by norm_num [cell12370])
      exact ⟨E.1,E.2.trans (by norm_num [cell12370])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy47 (n := 12370) (by norm_num)
        (q := 1 - (cell12370 ⟨47,by decide⟩).lower)
        (by norm_num [cell12370]) (by norm_num [cell12370])
      exact ⟨E.1,E.2.trans (by norm_num [cell12370])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy48 (n := 12370) (by norm_num)
        (q := 1 - (cell12370 ⟨48,by decide⟩).lower)
        (by norm_num [cell12370]) (by norm_num [cell12370])
      exact ⟨E.1,E.2.trans (by norm_num [cell12370])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy49 (n := 12370) (by norm_num)
        (q := 1 - (cell12370 ⟨49,by decide⟩).lower)
        (by norm_num [cell12370]) (by norm_num [cell12370])
      exact ⟨E.1,E.2.trans (by norm_num [cell12370])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy50 (n := 12370) (by norm_num)
        (q := 1 - (cell12370 ⟨50,by decide⟩).lower)
        (by norm_num [cell12370]) (by norm_num [cell12370])
      exact ⟨E.1,E.2.trans (by norm_num [cell12370])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy51 (n := 12370) (by norm_num)
        (q := 1 - (cell12370 ⟨51,by decide⟩).lower)
        (by norm_num [cell12370]) (by norm_num [cell12370])
      exact ⟨E.1,E.2.trans (by norm_num [cell12370])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy52 (n := 12370) (by norm_num)
        (q := 1 - (cell12370 ⟨52,by decide⟩).lower)
        (by norm_num [cell12370]) (by norm_num [cell12370])
      exact ⟨E.1,E.2.trans (by norm_num [cell12370])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12370

/-! Source-cell containment and simple scalar guards at 12370. -/
namespace BstLean.Part269.N12370
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12370)
open BstLean.Part268 (cell12370)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12370 ⟨10,by decide⟩).lower ∧ (cell12370 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12370 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12370 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12370 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12370 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12370 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12370,cell12370,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12370 ⟨11,by decide⟩).lower ∧ (cell12370 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12370 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12370 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12370 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12370 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12370 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12370,cell12370,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12370 ⟨12,by decide⟩).lower ∧ (cell12370 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12370 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12370 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12370 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12370 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12370 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12370,cell12370,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12370 ⟨13,by decide⟩).lower ∧ (cell12370 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12370 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12370 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12370 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12370 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12370 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12370,cell12370,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12370 ⟨14,by decide⟩).lower ∧ (cell12370 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12370 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12370 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12370 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12370 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12370 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12370,cell12370,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12370 ⟨15,by decide⟩).lower ∧ (cell12370 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12370 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12370 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12370 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12370 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12370 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12370,cell12370,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12370 ⟨16,by decide⟩).lower ∧ (cell12370 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12370 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12370 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12370 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12370 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12370 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12370,cell12370,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12370 ⟨17,by decide⟩).lower ∧ (cell12370 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12370 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12370 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12370 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12370 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12370 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12370,cell12370,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12370 ⟨18,by decide⟩).lower ∧ (cell12370 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12370 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12370 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12370 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12370 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12370 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12370,cell12370,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12370 ⟨19,by decide⟩).lower ∧ (cell12370 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12370 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12370 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12370 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12370 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12370 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12370,cell12370,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12370 ⟨20,by decide⟩).lower ∧ (cell12370 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12370 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12370 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12370 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12370 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12370 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12370,cell12370,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12370 ⟨21,by decide⟩).lower ∧ (cell12370 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12370 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12370 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12370 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12370 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12370 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12370,cell12370,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12370 ⟨22,by decide⟩).lower ∧ (cell12370 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12370 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12370 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12370 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12370 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12370 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12370,cell12370,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12370 ⟨23,by decide⟩).lower ∧ (cell12370 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12370 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12370 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12370 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12370 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12370 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12370,cell12370,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12370 ⟨24,by decide⟩).lower ∧ (cell12370 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12370 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12370 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12370 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12370 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12370 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12370,cell12370,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12370 ⟨25,by decide⟩).lower ∧ (cell12370 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12370 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12370 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12370 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12370 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12370 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12370,cell12370,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12370 ⟨26,by decide⟩).lower ∧ (cell12370 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12370 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12370 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12370 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12370 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12370 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12370,cell12370,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12370 ⟨27,by decide⟩).lower ∧ (cell12370 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12370 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12370 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12370 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12370 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12370 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12370,cell12370,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12370 ⟨28,by decide⟩).lower ∧ (cell12370 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12370 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12370 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12370 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12370 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12370 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12370,cell12370,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12370 ⟨29,by decide⟩).lower ∧ (cell12370 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12370 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12370 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12370 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12370 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12370 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12370,cell12370,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12370 ⟨30,by decide⟩).lower ∧ (cell12370 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12370 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12370 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12370 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12370 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12370 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12370,cell12370,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12370 ⟨31,by decide⟩).lower ∧ (cell12370 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12370 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12370 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12370 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12370 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12370 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12370,cell12370,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12370 ⟨32,by decide⟩).lower ∧ (cell12370 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12370 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12370 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12370 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12370 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12370 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12370,cell12370,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12370 ⟨33,by decide⟩).lower ∧ (cell12370 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12370 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12370 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12370 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12370 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12370 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12370,cell12370,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12370 ⟨34,by decide⟩).lower ∧ (cell12370 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12370 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12370 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12370 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12370 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12370 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12370,cell12370,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12370 ⟨35,by decide⟩).lower ∧ (cell12370 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12370 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12370 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12370 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12370 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12370 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12370,cell12370,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12370 ⟨36,by decide⟩).lower ∧ (cell12370 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12370 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12370 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12370 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12370 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12370 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12370,cell12370,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12370 ⟨37,by decide⟩).lower ∧ (cell12370 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12370 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12370 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12370 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12370 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12370 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12370,cell12370,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12370 ⟨38,by decide⟩).lower ∧ (cell12370 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12370 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12370 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12370 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12370 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12370 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12370,cell12370,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12370 ⟨39,by decide⟩).lower ∧ (cell12370 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12370 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12370 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12370 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12370 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12370 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12370,cell12370,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12370 ⟨40,by decide⟩).lower ∧ (cell12370 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12370 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12370 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12370 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12370 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12370 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12370,cell12370,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12370 ⟨41,by decide⟩).lower ∧ (cell12370 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12370 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12370 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12370 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12370 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12370 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12370,cell12370,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12370 ⟨42,by decide⟩).lower ∧ (cell12370 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12370 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12370 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12370 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12370 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12370 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12370,cell12370,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12370 ⟨43,by decide⟩).lower ∧ (cell12370 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12370 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12370 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12370 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12370 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12370 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12370,cell12370,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12370 ⟨44,by decide⟩).lower ∧ (cell12370 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12370 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12370 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12370 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12370 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12370 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12370,cell12370,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12370 ⟨45,by decide⟩).lower ∧ (cell12370 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12370 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12370 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12370 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12370 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12370 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12370,cell12370,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12370 ⟨46,by decide⟩).lower ∧ (cell12370 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12370 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12370 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12370 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12370 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12370 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12370,cell12370,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12370 ⟨47,by decide⟩).lower ∧ (cell12370 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12370 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12370 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12370 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12370 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12370 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12370,cell12370,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12370 ⟨48,by decide⟩).lower ∧ (cell12370 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12370 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12370 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12370 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12370 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12370 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12370,cell12370,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12370 ⟨49,by decide⟩).lower ∧ (cell12370 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12370 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12370 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12370 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12370 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12370 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12370,cell12370,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12370 ⟨50,by decide⟩).lower ∧ (cell12370 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12370 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12370 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12370 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12370 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12370 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12370,cell12370,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12370 ⟨51,by decide⟩).lower ∧ (cell12370 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12370 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12370 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12370 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12370 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12370 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12370,cell12370,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12370 ⟨52,by decide⟩).lower ∧ (cell12370 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12370 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12370 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12370 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12370 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12370 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12370,cell12370,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12370 i).lower ∧
    (cell12370 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12370 i).upper ≤ (0.532 : ℝ) ∧
    (cell12370 i).centre ≤ (0.1 : ℝ) ∧ (cell12370 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12370 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12370 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12370

/-! The local source numeric instances at 12370 have no network premises. -/
namespace BstLean.Part269.N12370
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12370)
open BstLean.Part268 (cell12370)

noncomputable def sourceNumerics12370 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12370 (cell12370 i)
      scalarRow12370.M scalarRow12370.H scalarRow12370.xi := by
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
    energy_allowance := scalarRow12370.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12370]
    centre_nonneg := (scalarRow12370.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D0.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12370])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12370
/-! Actual 12371 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12371
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12371 ≤ (1.036286475529 : ℝ) := by
  have hr : (111.224997190379 : ℝ) ≤ √(12371 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.224997190379 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12371 12371 (11 / 1000) ≤
    (0.008594175329 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12371) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.224997190379 : ℝ) ≤ √(12371 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12371)
  have hdiv : K / √(12371 : ℝ) ≤ K / 111.224997190379 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.224997190379 ≤ (0.008594175329 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12371.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12371 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12371 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12371 := gPlus_lower 12371
end BstLean.Part269.N12371

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12371
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036286475528 : ℝ) ≤ wn 12371 := by
  have hn : √(12371 : ℝ) ≤ 111.224997190380 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12371 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.224997190380 ≤ 2 / √(12371 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000258698645 : ℝ) ≤ rhoBar 12371 BstLean.Part154.csC ∧
    rhoBar 12371 BstLean.Part154.csC ≤ 0.000258699046 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036286475528 : ℝ) / (1.295212 * 12371) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036286475529 : ℝ) / (1.29521 * 12371) := by gcongr
      _ ≤ (0.000258699046 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12371 BstLean.Part154.csC) ≤ 0.001034863110 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12371 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12371 BstLean.Part154.csC) (piBar (rhoBar 12371 BstLean.Part154.csC)) ≤ 0.000197596325 ∧
    cc1 (rhoBar 12371 BstLean.Part154.csC) (piBar (rhoBar 12371 BstLean.Part154.csC)) ≤ 0.000125731803 ∧
    cc2 (rhoBar 12371 BstLean.Part154.csC) ≤ 0.000072988213 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12371 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12371 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12371 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12371 BstLean.Part154.csC * nuR (rhoBar 12371 BstLean.Part154.csC)) ≤ 0.000517414824 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000258699046 : ℝ) * 0.001034863110 := by gcongr
      _ ≤ (0.000517414824 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12371 BstLean.Part154.csC) * nuR (rhoBar 12371 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001034863110 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12371 BstLean.Part154.csC) * rhoBar 12371 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000258699046 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000258699046 / 2 + 0.399 * 0.001034863110 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000197596325 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000517414824 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125731803 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000258699046 / 1.414213562 := by gcongr
      _ ≤ (0.000072988213 : ℝ) := by norm_num

end BstLean.Part269.N12371

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12371
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12371 BstLean.Part154.csC) (piBar (rhoBar 12371 BstLean.Part154.csC)) ≤ 1.68614E-7 := by
  have hr0 : 0 ≤ rhoBar 12371 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12371 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12371 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12371 BstLean.Part154.csC) (piBar (rhoBar 12371 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12371 BstLean.Part154.csC) (piBar (rhoBar 12371 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12371 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000197596325 : ℝ) ^ 2 + 0.000125731803 ^ 2 + 3 * 0.000072988213 ^ 2 +
        2 * 0.797885 * 0.000197596325 * 0.000125731803 + 2 * 0.000197596325 * 0.000072988213 +
        4 * 0.797885 * 0.000125731803 * 0.000072988213 := by gcongr
    _ ≤ (1.68614E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12371 BstLean.Part154.csC Θ ≤ 0.002701713537 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12371 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12371 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12371 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12371 BstLean.Part154.csC) (piBar (rhoBar 12371 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12371 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036286475529 * 1.68614E-7 / (0.000258698645 : ℝ) := by gcongr
    _ ≤ 0.002701713537 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12371 BstLean.Part154.csC Θ ≤ 0.002999069831 + 0.000682676357 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12371 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12371 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12371 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036286475529 : ℝ) * ((2 * Θ * 0.000258699046 +
        (6863 / 10000) * 0.000258699046 * 12371 * 0.001034863110) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002999069831 + 0.000682676357 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12371 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12371 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12371 0.011 Θ ∧ gammaRatio 12371 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12371 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036286475529 : ℝ) * 0.525 / ((1 - 0.011) * 12371) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12371 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12371 0.011 Θ) :=
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
    badAllowance 12371 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12371 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12371 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12371 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12371 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12371 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12371 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12371 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12371 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12371 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12371 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036286475529 : ℝ) * 12371 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12371 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004099069831 + 0.003384389894 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12371

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12371
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12371 BstLean.Part154.csC) (piBar (rhoBar 12371 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12371 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12371 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12371 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12371 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12371 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12371 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12371 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12371 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12371 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12371 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12371 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12371 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12371 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12371 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053185246555 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12371) ≤ 0.010737132940 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12371 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036286475529)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010737132940 + 2 * 0.737676 / 12371) := by gcongr
    _ ≤ (0.053185246555 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12371 12 ≤ 0.0015 := by
  exact BstLean.Part269.S0.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12371

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12371
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560488294252 : ℝ) ≤ plow 12371 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12371) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053382474526)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001418399607) : eMP 12371 0.011 xi bn ≤ 0.001220697262 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12371 : ℝ) * (1 - 0.011))) ≤ 0.000603495050 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001418399607 / (12371 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000603495050 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000603495050 : ℝ) + 3.141593 * 0.053382474526 / (12371 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001220697262 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053382474526)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001418399607) : PiBarMP 12371 12 0.011 xi bn ≤ 0.163404942525 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12371 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037661646367 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.611568111115 : ℝ) ≤ √((12371 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.224997190379 : ℝ) ≤ √(12371 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12371) ≤ 0.125263282668 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037661646367 + 0.053382474526 * 1.772454 / (2 * (110.611568111115 : ℝ))) * (1 + 0.001220697262) +
        8 / (12371 * 111.224997190379) + 0.125263282668 := by gcongr
    _ ≤ (0.163404942525 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053382474526)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001418399607) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284231723538) :
    parallelOracle 12371 0.011 xi bn cd ≤ 0.164425410207 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12371 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12371 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560488294252 : ℝ) ≤ plow 12371 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.224997190379 : ℝ) ≤ √(12371 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284231723538 : ℝ) / (2 * 0.560488294252 * 111.224997190379)) * 0.163404942525 +
        0.284231723538 ^ 2 / (2 * 0.560488294252 * 111.224997190379) := by gcongr
    _ ≤ (0.164425410207 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053382474526) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001418399607)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284231723538) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12371 12371 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560488294252 : ℝ) ≤ plow 12371 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.224997190379 : ℝ) ≤ √(12371 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12371 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12371 Θ 1.22 ≤ 0.011922684051 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.224997190379 := by gcongr <;> linarith
      _ ≤ (0.011922684051 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12371 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12371 12371 0.011 ≤ 0.008594175329 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12371 12371 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12371 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12371 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12371 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12371 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164425410207 + 0.011922684051 + (0.008594175329 : ℝ) *
        (1 + 2 * (0.284231723538 + 0.011922684051) / (0.560488294252 * 111.224997190379))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12371]

end BstLean.Part269.N12371

/-! The original eight local profiles supply actual 12371 moment certificates. -/
namespace BstLean.Part269.N12371
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12371 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12371 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12371 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053382474526 ∧
    0 ≤ bN 12371 BstLean.Part154.csC (groupTheta g) ∧ bN 12371 BstLean.Part154.csC (groupTheta g) ≤ 0.001418399607 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12371 12371 0.011
      (momentAllowance 12371 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12371 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12371 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12371 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12371 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12371 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231046476983 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12371 0.011
      (momentAllowance 12371 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12371 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12371
/-! The actual computed-centre upper energy formula at 12371. -/
namespace BstLean.Part269.N12371
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12371

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12371
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12371)
open BstLean.Part268 (cell12371)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086515654200
  | 2 => 0.087478823057
  | 3 => 0.088443357418
  | 4 => 0.089411398664
  | 5 => 0.090385509581
  | 6 => 0.091368733289
  | 7 => 0.092364657052
  | 8 => 0.093377480931
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12371 12371 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12371 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12371

/-! Actual upper energy certificates on all 43 source endpoints at 12371. -/
namespace BstLean.Part269.N12371
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12371)
open BstLean.Part268 (cell12371)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12371 (gMinus 12371) (1 - (cell12371 i).lower) ≤ 1 ∧
    energyUpper 12371 (gMinus 12371) (BstLean.Part211.gPlus 12371)
      (finiteEnergy 12371 12371 0.011) (1 - (cell12371 i).lower) ≤
      (cell12371 i).energy := by
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
      have E := BstLean.Part269.S0.uniformEnergy10 (n := 12371) (by norm_num)
        (q := 1 - (cell12371 ⟨10,by decide⟩).lower)
        (by norm_num [cell12371]) (by norm_num [cell12371])
      exact ⟨E.1,E.2.trans (by norm_num [cell12371])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy11 (n := 12371) (by norm_num)
        (q := 1 - (cell12371 ⟨11,by decide⟩).lower)
        (by norm_num [cell12371]) (by norm_num [cell12371])
      exact ⟨E.1,E.2.trans (by norm_num [cell12371])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy12 (n := 12371) (by norm_num)
        (q := 1 - (cell12371 ⟨12,by decide⟩).lower)
        (by norm_num [cell12371]) (by norm_num [cell12371])
      exact ⟨E.1,E.2.trans (by norm_num [cell12371])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy13 (n := 12371) (by norm_num)
        (q := 1 - (cell12371 ⟨13,by decide⟩).lower)
        (by norm_num [cell12371]) (by norm_num [cell12371])
      exact ⟨E.1,E.2.trans (by norm_num [cell12371])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy14 (n := 12371) (by norm_num)
        (q := 1 - (cell12371 ⟨14,by decide⟩).lower)
        (by norm_num [cell12371]) (by norm_num [cell12371])
      exact ⟨E.1,E.2.trans (by norm_num [cell12371])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy15 (n := 12371) (by norm_num)
        (q := 1 - (cell12371 ⟨15,by decide⟩).lower)
        (by norm_num [cell12371]) (by norm_num [cell12371])
      exact ⟨E.1,E.2.trans (by norm_num [cell12371])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy16 (n := 12371) (by norm_num)
        (q := 1 - (cell12371 ⟨16,by decide⟩).lower)
        (by norm_num [cell12371]) (by norm_num [cell12371])
      exact ⟨E.1,E.2.trans (by norm_num [cell12371])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy17 (n := 12371) (by norm_num)
        (q := 1 - (cell12371 ⟨17,by decide⟩).lower)
        (by norm_num [cell12371]) (by norm_num [cell12371])
      exact ⟨E.1,E.2.trans (by norm_num [cell12371])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy18 (n := 12371) (by norm_num)
        (q := 1 - (cell12371 ⟨18,by decide⟩).lower)
        (by norm_num [cell12371]) (by norm_num [cell12371])
      exact ⟨E.1,E.2.trans (by norm_num [cell12371])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy19 (n := 12371) (by norm_num)
        (q := 1 - (cell12371 ⟨19,by decide⟩).lower)
        (by norm_num [cell12371]) (by norm_num [cell12371])
      exact ⟨E.1,E.2.trans (by norm_num [cell12371])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy20 (n := 12371) (by norm_num)
        (q := 1 - (cell12371 ⟨20,by decide⟩).lower)
        (by norm_num [cell12371]) (by norm_num [cell12371])
      exact ⟨E.1,E.2.trans (by norm_num [cell12371])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy21 (n := 12371) (by norm_num)
        (q := 1 - (cell12371 ⟨21,by decide⟩).lower)
        (by norm_num [cell12371]) (by norm_num [cell12371])
      exact ⟨E.1,E.2.trans (by norm_num [cell12371])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy22 (n := 12371) (by norm_num)
        (q := 1 - (cell12371 ⟨22,by decide⟩).lower)
        (by norm_num [cell12371]) (by norm_num [cell12371])
      exact ⟨E.1,E.2.trans (by norm_num [cell12371])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy23 (n := 12371) (by norm_num)
        (q := 1 - (cell12371 ⟨23,by decide⟩).lower)
        (by norm_num [cell12371]) (by norm_num [cell12371])
      exact ⟨E.1,E.2.trans (by norm_num [cell12371])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy24 (n := 12371) (by norm_num)
        (q := 1 - (cell12371 ⟨24,by decide⟩).lower)
        (by norm_num [cell12371]) (by norm_num [cell12371])
      exact ⟨E.1,E.2.trans (by norm_num [cell12371])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy25 (n := 12371) (by norm_num)
        (q := 1 - (cell12371 ⟨25,by decide⟩).lower)
        (by norm_num [cell12371]) (by norm_num [cell12371])
      exact ⟨E.1,E.2.trans (by norm_num [cell12371])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy26 (n := 12371) (by norm_num)
        (q := 1 - (cell12371 ⟨26,by decide⟩).lower)
        (by norm_num [cell12371]) (by norm_num [cell12371])
      exact ⟨E.1,E.2.trans (by norm_num [cell12371])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy27 (n := 12371) (by norm_num)
        (q := 1 - (cell12371 ⟨27,by decide⟩).lower)
        (by norm_num [cell12371]) (by norm_num [cell12371])
      exact ⟨E.1,E.2.trans (by norm_num [cell12371])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy28 (n := 12371) (by norm_num)
        (q := 1 - (cell12371 ⟨28,by decide⟩).lower)
        (by norm_num [cell12371]) (by norm_num [cell12371])
      exact ⟨E.1,E.2.trans (by norm_num [cell12371])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy29 (n := 12371) (by norm_num)
        (q := 1 - (cell12371 ⟨29,by decide⟩).lower)
        (by norm_num [cell12371]) (by norm_num [cell12371])
      exact ⟨E.1,E.2.trans (by norm_num [cell12371])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy30 (n := 12371) (by norm_num)
        (q := 1 - (cell12371 ⟨30,by decide⟩).lower)
        (by norm_num [cell12371]) (by norm_num [cell12371])
      exact ⟨E.1,E.2.trans (by norm_num [cell12371])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy31 (n := 12371) (by norm_num)
        (q := 1 - (cell12371 ⟨31,by decide⟩).lower)
        (by norm_num [cell12371]) (by norm_num [cell12371])
      exact ⟨E.1,E.2.trans (by norm_num [cell12371])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy32 (n := 12371) (by norm_num)
        (q := 1 - (cell12371 ⟨32,by decide⟩).lower)
        (by norm_num [cell12371]) (by norm_num [cell12371])
      exact ⟨E.1,E.2.trans (by norm_num [cell12371])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy33 (n := 12371) (by norm_num)
        (q := 1 - (cell12371 ⟨33,by decide⟩).lower)
        (by norm_num [cell12371]) (by norm_num [cell12371])
      exact ⟨E.1,E.2.trans (by norm_num [cell12371])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy34 (n := 12371) (by norm_num)
        (q := 1 - (cell12371 ⟨34,by decide⟩).lower)
        (by norm_num [cell12371]) (by norm_num [cell12371])
      exact ⟨E.1,E.2.trans (by norm_num [cell12371])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy35 (n := 12371) (by norm_num)
        (q := 1 - (cell12371 ⟨35,by decide⟩).lower)
        (by norm_num [cell12371]) (by norm_num [cell12371])
      exact ⟨E.1,E.2.trans (by norm_num [cell12371])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy36 (n := 12371) (by norm_num)
        (q := 1 - (cell12371 ⟨36,by decide⟩).lower)
        (by norm_num [cell12371]) (by norm_num [cell12371])
      exact ⟨E.1,E.2.trans (by norm_num [cell12371])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy37 (n := 12371) (by norm_num)
        (q := 1 - (cell12371 ⟨37,by decide⟩).lower)
        (by norm_num [cell12371]) (by norm_num [cell12371])
      exact ⟨E.1,E.2.trans (by norm_num [cell12371])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy38 (n := 12371) (by norm_num)
        (q := 1 - (cell12371 ⟨38,by decide⟩).lower)
        (by norm_num [cell12371]) (by norm_num [cell12371])
      exact ⟨E.1,E.2.trans (by norm_num [cell12371])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy39 (n := 12371) (by norm_num)
        (q := 1 - (cell12371 ⟨39,by decide⟩).lower)
        (by norm_num [cell12371]) (by norm_num [cell12371])
      exact ⟨E.1,E.2.trans (by norm_num [cell12371])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy40 (n := 12371) (by norm_num)
        (q := 1 - (cell12371 ⟨40,by decide⟩).lower)
        (by norm_num [cell12371]) (by norm_num [cell12371])
      exact ⟨E.1,E.2.trans (by norm_num [cell12371])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy41 (n := 12371) (by norm_num)
        (q := 1 - (cell12371 ⟨41,by decide⟩).lower)
        (by norm_num [cell12371]) (by norm_num [cell12371])
      exact ⟨E.1,E.2.trans (by norm_num [cell12371])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy42 (n := 12371) (by norm_num)
        (q := 1 - (cell12371 ⟨42,by decide⟩).lower)
        (by norm_num [cell12371]) (by norm_num [cell12371])
      exact ⟨E.1,E.2.trans (by norm_num [cell12371])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy43 (n := 12371) (by norm_num)
        (q := 1 - (cell12371 ⟨43,by decide⟩).lower)
        (by norm_num [cell12371]) (by norm_num [cell12371])
      exact ⟨E.1,E.2.trans (by norm_num [cell12371])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy44 (n := 12371) (by norm_num)
        (q := 1 - (cell12371 ⟨44,by decide⟩).lower)
        (by norm_num [cell12371]) (by norm_num [cell12371])
      exact ⟨E.1,E.2.trans (by norm_num [cell12371])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy45 (n := 12371) (by norm_num)
        (q := 1 - (cell12371 ⟨45,by decide⟩).lower)
        (by norm_num [cell12371]) (by norm_num [cell12371])
      exact ⟨E.1,E.2.trans (by norm_num [cell12371])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy46 (n := 12371) (by norm_num)
        (q := 1 - (cell12371 ⟨46,by decide⟩).lower)
        (by norm_num [cell12371]) (by norm_num [cell12371])
      exact ⟨E.1,E.2.trans (by norm_num [cell12371])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy47 (n := 12371) (by norm_num)
        (q := 1 - (cell12371 ⟨47,by decide⟩).lower)
        (by norm_num [cell12371]) (by norm_num [cell12371])
      exact ⟨E.1,E.2.trans (by norm_num [cell12371])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy48 (n := 12371) (by norm_num)
        (q := 1 - (cell12371 ⟨48,by decide⟩).lower)
        (by norm_num [cell12371]) (by norm_num [cell12371])
      exact ⟨E.1,E.2.trans (by norm_num [cell12371])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy49 (n := 12371) (by norm_num)
        (q := 1 - (cell12371 ⟨49,by decide⟩).lower)
        (by norm_num [cell12371]) (by norm_num [cell12371])
      exact ⟨E.1,E.2.trans (by norm_num [cell12371])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy50 (n := 12371) (by norm_num)
        (q := 1 - (cell12371 ⟨50,by decide⟩).lower)
        (by norm_num [cell12371]) (by norm_num [cell12371])
      exact ⟨E.1,E.2.trans (by norm_num [cell12371])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy51 (n := 12371) (by norm_num)
        (q := 1 - (cell12371 ⟨51,by decide⟩).lower)
        (by norm_num [cell12371]) (by norm_num [cell12371])
      exact ⟨E.1,E.2.trans (by norm_num [cell12371])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy52 (n := 12371) (by norm_num)
        (q := 1 - (cell12371 ⟨52,by decide⟩).lower)
        (by norm_num [cell12371]) (by norm_num [cell12371])
      exact ⟨E.1,E.2.trans (by norm_num [cell12371])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12371

/-! Source-cell containment and simple scalar guards at 12371. -/
namespace BstLean.Part269.N12371
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12371)
open BstLean.Part268 (cell12371)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12371 ⟨10,by decide⟩).lower ∧ (cell12371 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12371 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12371 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12371 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12371 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12371 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12371,cell12371,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12371 ⟨11,by decide⟩).lower ∧ (cell12371 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12371 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12371 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12371 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12371 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12371 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12371,cell12371,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12371 ⟨12,by decide⟩).lower ∧ (cell12371 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12371 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12371 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12371 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12371 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12371 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12371,cell12371,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12371 ⟨13,by decide⟩).lower ∧ (cell12371 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12371 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12371 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12371 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12371 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12371 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12371,cell12371,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12371 ⟨14,by decide⟩).lower ∧ (cell12371 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12371 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12371 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12371 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12371 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12371 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12371,cell12371,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12371 ⟨15,by decide⟩).lower ∧ (cell12371 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12371 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12371 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12371 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12371 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12371 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12371,cell12371,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12371 ⟨16,by decide⟩).lower ∧ (cell12371 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12371 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12371 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12371 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12371 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12371 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12371,cell12371,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12371 ⟨17,by decide⟩).lower ∧ (cell12371 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12371 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12371 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12371 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12371 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12371 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12371,cell12371,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12371 ⟨18,by decide⟩).lower ∧ (cell12371 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12371 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12371 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12371 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12371 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12371 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12371,cell12371,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12371 ⟨19,by decide⟩).lower ∧ (cell12371 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12371 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12371 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12371 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12371 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12371 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12371,cell12371,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12371 ⟨20,by decide⟩).lower ∧ (cell12371 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12371 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12371 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12371 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12371 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12371 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12371,cell12371,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12371 ⟨21,by decide⟩).lower ∧ (cell12371 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12371 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12371 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12371 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12371 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12371 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12371,cell12371,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12371 ⟨22,by decide⟩).lower ∧ (cell12371 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12371 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12371 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12371 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12371 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12371 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12371,cell12371,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12371 ⟨23,by decide⟩).lower ∧ (cell12371 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12371 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12371 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12371 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12371 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12371 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12371,cell12371,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12371 ⟨24,by decide⟩).lower ∧ (cell12371 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12371 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12371 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12371 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12371 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12371 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12371,cell12371,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12371 ⟨25,by decide⟩).lower ∧ (cell12371 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12371 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12371 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12371 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12371 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12371 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12371,cell12371,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12371 ⟨26,by decide⟩).lower ∧ (cell12371 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12371 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12371 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12371 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12371 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12371 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12371,cell12371,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12371 ⟨27,by decide⟩).lower ∧ (cell12371 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12371 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12371 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12371 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12371 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12371 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12371,cell12371,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12371 ⟨28,by decide⟩).lower ∧ (cell12371 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12371 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12371 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12371 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12371 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12371 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12371,cell12371,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12371 ⟨29,by decide⟩).lower ∧ (cell12371 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12371 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12371 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12371 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12371 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12371 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12371,cell12371,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12371 ⟨30,by decide⟩).lower ∧ (cell12371 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12371 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12371 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12371 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12371 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12371 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12371,cell12371,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12371 ⟨31,by decide⟩).lower ∧ (cell12371 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12371 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12371 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12371 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12371 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12371 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12371,cell12371,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12371 ⟨32,by decide⟩).lower ∧ (cell12371 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12371 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12371 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12371 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12371 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12371 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12371,cell12371,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12371 ⟨33,by decide⟩).lower ∧ (cell12371 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12371 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12371 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12371 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12371 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12371 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12371,cell12371,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12371 ⟨34,by decide⟩).lower ∧ (cell12371 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12371 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12371 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12371 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12371 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12371 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12371,cell12371,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12371 ⟨35,by decide⟩).lower ∧ (cell12371 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12371 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12371 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12371 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12371 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12371 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12371,cell12371,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12371 ⟨36,by decide⟩).lower ∧ (cell12371 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12371 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12371 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12371 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12371 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12371 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12371,cell12371,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12371 ⟨37,by decide⟩).lower ∧ (cell12371 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12371 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12371 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12371 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12371 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12371 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12371,cell12371,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12371 ⟨38,by decide⟩).lower ∧ (cell12371 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12371 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12371 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12371 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12371 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12371 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12371,cell12371,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12371 ⟨39,by decide⟩).lower ∧ (cell12371 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12371 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12371 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12371 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12371 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12371 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12371,cell12371,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12371 ⟨40,by decide⟩).lower ∧ (cell12371 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12371 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12371 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12371 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12371 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12371 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12371,cell12371,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12371 ⟨41,by decide⟩).lower ∧ (cell12371 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12371 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12371 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12371 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12371 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12371 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12371,cell12371,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12371 ⟨42,by decide⟩).lower ∧ (cell12371 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12371 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12371 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12371 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12371 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12371 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12371,cell12371,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12371 ⟨43,by decide⟩).lower ∧ (cell12371 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12371 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12371 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12371 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12371 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12371 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12371,cell12371,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12371 ⟨44,by decide⟩).lower ∧ (cell12371 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12371 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12371 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12371 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12371 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12371 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12371,cell12371,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12371 ⟨45,by decide⟩).lower ∧ (cell12371 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12371 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12371 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12371 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12371 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12371 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12371,cell12371,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12371 ⟨46,by decide⟩).lower ∧ (cell12371 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12371 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12371 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12371 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12371 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12371 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12371,cell12371,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12371 ⟨47,by decide⟩).lower ∧ (cell12371 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12371 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12371 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12371 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12371 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12371 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12371,cell12371,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12371 ⟨48,by decide⟩).lower ∧ (cell12371 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12371 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12371 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12371 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12371 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12371 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12371,cell12371,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12371 ⟨49,by decide⟩).lower ∧ (cell12371 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12371 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12371 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12371 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12371 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12371 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12371,cell12371,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12371 ⟨50,by decide⟩).lower ∧ (cell12371 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12371 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12371 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12371 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12371 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12371 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12371,cell12371,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12371 ⟨51,by decide⟩).lower ∧ (cell12371 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12371 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12371 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12371 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12371 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12371 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12371,cell12371,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12371 ⟨52,by decide⟩).lower ∧ (cell12371 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12371 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12371 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12371 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12371 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12371 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12371,cell12371,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12371 i).lower ∧
    (cell12371 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12371 i).upper ≤ (0.532 : ℝ) ∧
    (cell12371 i).centre ≤ (0.1 : ℝ) ∧ (cell12371 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12371 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12371 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12371

/-! The local source numeric instances at 12371 have no network premises. -/
namespace BstLean.Part269.N12371
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12371)
open BstLean.Part268 (cell12371)

noncomputable def sourceNumerics12371 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12371 (cell12371 i)
      scalarRow12371.M scalarRow12371.H scalarRow12371.xi := by
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
    energy_allowance := scalarRow12371.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12371]
    centre_nonneg := (scalarRow12371.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D0.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12371])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12371
/-! Actual 12372 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12372
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12372 ≤ (1.036284995956 : ℝ) := by
  have hr : (111.229492491874 : ℝ) ≤ √(12372 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.229492491874 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12372 12372 (11 / 1000) ≤
    (0.008593827996 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12372) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.229492491874 : ℝ) ≤ √(12372 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12372)
  have hdiv : K / √(12372 : ℝ) ≤ K / 111.229492491874 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.229492491874 ≤ (0.008593827996 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12372.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12372 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12372 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12372 := gPlus_lower 12372
end BstLean.Part269.N12372

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12372
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036284995955 : ℝ) ≤ wn 12372 := by
  have hn : √(12372 : ℝ) ≤ 111.229492491875 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12372 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.229492491875 ≤ 2 / √(12372 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000258677366 : ℝ) ≤ rhoBar 12372 BstLean.Part154.csC ∧
    rhoBar 12372 BstLean.Part154.csC ≤ 0.000258677766 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036284995955 : ℝ) / (1.295212 * 12372) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036284995956 : ℝ) / (1.29521 * 12372) := by gcongr
      _ ≤ (0.000258677766 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12372 BstLean.Part154.csC) ≤ 0.001034777979 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12372 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12372 BstLean.Part154.csC) (piBar (rhoBar 12372 BstLean.Part154.csC)) ≤ 0.000197580071 ∧
    cc1 (rhoBar 12372 BstLean.Part154.csC) (piBar (rhoBar 12372 BstLean.Part154.csC)) ≤ 0.000125721460 ∧
    cc2 (rhoBar 12372 BstLean.Part154.csC) ≤ 0.000072982209 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12372 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12372 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12372 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12372 BstLean.Part154.csC * nuR (rhoBar 12372 BstLean.Part154.csC)) ≤ 0.000517372261 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000258677766 : ℝ) * 0.001034777979 := by gcongr
      _ ≤ (0.000517372261 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12372 BstLean.Part154.csC) * nuR (rhoBar 12372 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001034777979 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12372 BstLean.Part154.csC) * rhoBar 12372 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000258677766 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000258677766 / 2 + 0.399 * 0.001034777979 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000197580071 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000517372261 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125721460 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000258677766 / 1.414213562 := by gcongr
      _ ≤ (0.000072982209 : ℝ) := by norm_num

end BstLean.Part269.N12372

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12372
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12372 BstLean.Part154.csC) (piBar (rhoBar 12372 BstLean.Part154.csC)) ≤ 1.68586E-7 := by
  have hr0 : 0 ≤ rhoBar 12372 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12372 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12372 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12372 BstLean.Part154.csC) (piBar (rhoBar 12372 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12372 BstLean.Part154.csC) (piBar (rhoBar 12372 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12372 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000197580071 : ℝ) ^ 2 + 0.000125721460 ^ 2 + 3 * 0.000072982209 ^ 2 +
        2 * 0.797885 * 0.000197580071 * 0.000125721460 + 2 * 0.000197580071 * 0.000072982209 +
        4 * 0.797885 * 0.000125721460 * 0.000072982209 := by gcongr
    _ ≤ (1.68586E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12372 BstLean.Part154.csC Θ ≤ 0.002701483242 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12372 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12372 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12372 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12372 BstLean.Part154.csC) (piBar (rhoBar 12372 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12372 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036284995956 * 1.68586E-7 / (0.000258677366 : ℝ) := by gcongr
    _ ≤ 0.002701483242 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12372 BstLean.Part154.csC Θ ≤ 0.002998814548 + 0.000682619227 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12372 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12372 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12372 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036284995956 : ℝ) * ((2 * Θ * 0.000258677766 +
        (6863 / 10000) * 0.000258677766 * 12372 * 0.001034777979) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002998814548 + 0.000682619227 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12372 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12372 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12372 0.011 Θ ∧ gammaRatio 12372 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12372 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036284995956 : ℝ) * 0.525 / ((1 - 0.011) * 12372) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12372 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12372 0.011 Θ) :=
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
    badAllowance 12372 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12372 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12372 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12372 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12372 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12372 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12372 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12372 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12372 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12372 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12372 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036284995956 : ℝ) * 12372 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12372 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004098814548 + 0.003384102469 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12372

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12372
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12372 BstLean.Part154.csC) (piBar (rhoBar 12372 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12372 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12372 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12372 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12372 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12372 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12372 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12372 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12372 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12372 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12372 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12372 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12372 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12372 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12372 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053183073483 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12372) ≤ 0.010736699003 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12372 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036284995956)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010736699003 + 2 * 0.737676 / 12372) := by gcongr
    _ ≤ (0.053183073483 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12372 12 ≤ 0.0015 := by
  exact BstLean.Part269.S0.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12372

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12372
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560488341909 : ℝ) ≤ plow 12372 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12372) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053382068345)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001418278703) : eMP 12372 0.011 xi bn ≤ 0.001220595830 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12372 : ℝ) * (1 - 0.011))) ≤ 0.000603444940 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001418278703 / (12372 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000603444940 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000603444940 : ℝ) + 3.141593 * 0.053382068345 / (12372 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001220595830 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053382068345)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001418278703) : PiBarMP 12372 12 0.011 xi bn ≤ 0.163398247792 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12372 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037660041198 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.616038620084 : ℝ) ≤ √((12372 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.229492491874 : ℝ) ≤ √(12372 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12372) ≤ 0.125258220196 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037660041198 + 0.053382068345 * 1.772454 / (2 * (110.616038620084 : ℝ))) * (1 + 0.001220595830) +
        8 / (12372 * 111.229492491874) + 0.125258220196 := by gcongr
    _ ≤ (0.163398247792 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053382068345)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001418278703) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284228671461) :
    parallelOracle 12372 0.011 xi bn cd ≤ 0.164418640970 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12372 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12372 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560488341909 : ℝ) ≤ plow 12372 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.229492491874 : ℝ) ≤ √(12372 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284228671461 : ℝ) / (2 * 0.560488341909 * 111.229492491874)) * 0.163398247792 +
        0.284228671461 ^ 2 / (2 * 0.560488341909 * 111.229492491874) := by gcongr
    _ ≤ (0.164418640970 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053382068345) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001418278703)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284228671461) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12372 12372 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560488341909 : ℝ) ≤ plow 12372 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.229492491874 : ℝ) ≤ √(12372 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12372 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12372 Θ 1.22 ≤ 0.011922202200 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.229492491874 := by gcongr <;> linarith
      _ ≤ (0.011922202200 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12372 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12372 12372 0.011 ≤ 0.008593827996 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12372 12372 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12372 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12372 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12372 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12372 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164418640970 + 0.011922202200 + (0.008593827996 : ℝ) *
        (1 + 2 * (0.284228671461 + 0.011922202200) / (0.560488341909 * 111.229492491874))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12372]

end BstLean.Part269.N12372

/-! The original eight local profiles supply actual 12372 moment certificates. -/
namespace BstLean.Part269.N12372
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12372 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12372 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12372 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053382068345 ∧
    0 ≤ bN 12372 BstLean.Part154.csC (groupTheta g) ∧ bN 12372 BstLean.Part154.csC (groupTheta g) ≤ 0.001418278703 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12372 12372 0.011
      (momentAllowance 12372 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12372 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12372 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12372 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12372 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12372 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231045597978 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12372 0.011
      (momentAllowance 12372 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12372 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12372
/-! The actual computed-centre upper energy formula at 12372. -/
namespace BstLean.Part269.N12372
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12372

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12372
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12372)
open BstLean.Part268 (cell12372)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086512313215
  | 2 => 0.087475410245
  | 3 => 0.088439860696
  | 4 => 0.089407803299
  | 5 => 0.090381797751
  | 6 => 0.091364883584
  | 7 => 0.092360643931
  | 8 => 0.093373274116
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12372 12372 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12372 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12372

/-! Actual upper energy certificates on all 43 source endpoints at 12372. -/
namespace BstLean.Part269.N12372
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12372)
open BstLean.Part268 (cell12372)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12372 (gMinus 12372) (1 - (cell12372 i).lower) ≤ 1 ∧
    energyUpper 12372 (gMinus 12372) (BstLean.Part211.gPlus 12372)
      (finiteEnergy 12372 12372 0.011) (1 - (cell12372 i).lower) ≤
      (cell12372 i).energy := by
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
      have E := BstLean.Part269.S0.uniformEnergy10 (n := 12372) (by norm_num)
        (q := 1 - (cell12372 ⟨10,by decide⟩).lower)
        (by norm_num [cell12372]) (by norm_num [cell12372])
      exact ⟨E.1,E.2.trans (by norm_num [cell12372])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy11 (n := 12372) (by norm_num)
        (q := 1 - (cell12372 ⟨11,by decide⟩).lower)
        (by norm_num [cell12372]) (by norm_num [cell12372])
      exact ⟨E.1,E.2.trans (by norm_num [cell12372])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy12 (n := 12372) (by norm_num)
        (q := 1 - (cell12372 ⟨12,by decide⟩).lower)
        (by norm_num [cell12372]) (by norm_num [cell12372])
      exact ⟨E.1,E.2.trans (by norm_num [cell12372])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy13 (n := 12372) (by norm_num)
        (q := 1 - (cell12372 ⟨13,by decide⟩).lower)
        (by norm_num [cell12372]) (by norm_num [cell12372])
      exact ⟨E.1,E.2.trans (by norm_num [cell12372])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy14 (n := 12372) (by norm_num)
        (q := 1 - (cell12372 ⟨14,by decide⟩).lower)
        (by norm_num [cell12372]) (by norm_num [cell12372])
      exact ⟨E.1,E.2.trans (by norm_num [cell12372])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy15 (n := 12372) (by norm_num)
        (q := 1 - (cell12372 ⟨15,by decide⟩).lower)
        (by norm_num [cell12372]) (by norm_num [cell12372])
      exact ⟨E.1,E.2.trans (by norm_num [cell12372])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy16 (n := 12372) (by norm_num)
        (q := 1 - (cell12372 ⟨16,by decide⟩).lower)
        (by norm_num [cell12372]) (by norm_num [cell12372])
      exact ⟨E.1,E.2.trans (by norm_num [cell12372])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy17 (n := 12372) (by norm_num)
        (q := 1 - (cell12372 ⟨17,by decide⟩).lower)
        (by norm_num [cell12372]) (by norm_num [cell12372])
      exact ⟨E.1,E.2.trans (by norm_num [cell12372])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy18 (n := 12372) (by norm_num)
        (q := 1 - (cell12372 ⟨18,by decide⟩).lower)
        (by norm_num [cell12372]) (by norm_num [cell12372])
      exact ⟨E.1,E.2.trans (by norm_num [cell12372])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy19 (n := 12372) (by norm_num)
        (q := 1 - (cell12372 ⟨19,by decide⟩).lower)
        (by norm_num [cell12372]) (by norm_num [cell12372])
      exact ⟨E.1,E.2.trans (by norm_num [cell12372])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy20 (n := 12372) (by norm_num)
        (q := 1 - (cell12372 ⟨20,by decide⟩).lower)
        (by norm_num [cell12372]) (by norm_num [cell12372])
      exact ⟨E.1,E.2.trans (by norm_num [cell12372])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy21 (n := 12372) (by norm_num)
        (q := 1 - (cell12372 ⟨21,by decide⟩).lower)
        (by norm_num [cell12372]) (by norm_num [cell12372])
      exact ⟨E.1,E.2.trans (by norm_num [cell12372])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy22 (n := 12372) (by norm_num)
        (q := 1 - (cell12372 ⟨22,by decide⟩).lower)
        (by norm_num [cell12372]) (by norm_num [cell12372])
      exact ⟨E.1,E.2.trans (by norm_num [cell12372])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy23 (n := 12372) (by norm_num)
        (q := 1 - (cell12372 ⟨23,by decide⟩).lower)
        (by norm_num [cell12372]) (by norm_num [cell12372])
      exact ⟨E.1,E.2.trans (by norm_num [cell12372])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy24 (n := 12372) (by norm_num)
        (q := 1 - (cell12372 ⟨24,by decide⟩).lower)
        (by norm_num [cell12372]) (by norm_num [cell12372])
      exact ⟨E.1,E.2.trans (by norm_num [cell12372])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy25 (n := 12372) (by norm_num)
        (q := 1 - (cell12372 ⟨25,by decide⟩).lower)
        (by norm_num [cell12372]) (by norm_num [cell12372])
      exact ⟨E.1,E.2.trans (by norm_num [cell12372])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy26 (n := 12372) (by norm_num)
        (q := 1 - (cell12372 ⟨26,by decide⟩).lower)
        (by norm_num [cell12372]) (by norm_num [cell12372])
      exact ⟨E.1,E.2.trans (by norm_num [cell12372])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy27 (n := 12372) (by norm_num)
        (q := 1 - (cell12372 ⟨27,by decide⟩).lower)
        (by norm_num [cell12372]) (by norm_num [cell12372])
      exact ⟨E.1,E.2.trans (by norm_num [cell12372])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy28 (n := 12372) (by norm_num)
        (q := 1 - (cell12372 ⟨28,by decide⟩).lower)
        (by norm_num [cell12372]) (by norm_num [cell12372])
      exact ⟨E.1,E.2.trans (by norm_num [cell12372])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy29 (n := 12372) (by norm_num)
        (q := 1 - (cell12372 ⟨29,by decide⟩).lower)
        (by norm_num [cell12372]) (by norm_num [cell12372])
      exact ⟨E.1,E.2.trans (by norm_num [cell12372])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy30 (n := 12372) (by norm_num)
        (q := 1 - (cell12372 ⟨30,by decide⟩).lower)
        (by norm_num [cell12372]) (by norm_num [cell12372])
      exact ⟨E.1,E.2.trans (by norm_num [cell12372])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy31 (n := 12372) (by norm_num)
        (q := 1 - (cell12372 ⟨31,by decide⟩).lower)
        (by norm_num [cell12372]) (by norm_num [cell12372])
      exact ⟨E.1,E.2.trans (by norm_num [cell12372])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy32 (n := 12372) (by norm_num)
        (q := 1 - (cell12372 ⟨32,by decide⟩).lower)
        (by norm_num [cell12372]) (by norm_num [cell12372])
      exact ⟨E.1,E.2.trans (by norm_num [cell12372])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy33 (n := 12372) (by norm_num)
        (q := 1 - (cell12372 ⟨33,by decide⟩).lower)
        (by norm_num [cell12372]) (by norm_num [cell12372])
      exact ⟨E.1,E.2.trans (by norm_num [cell12372])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy34 (n := 12372) (by norm_num)
        (q := 1 - (cell12372 ⟨34,by decide⟩).lower)
        (by norm_num [cell12372]) (by norm_num [cell12372])
      exact ⟨E.1,E.2.trans (by norm_num [cell12372])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy35 (n := 12372) (by norm_num)
        (q := 1 - (cell12372 ⟨35,by decide⟩).lower)
        (by norm_num [cell12372]) (by norm_num [cell12372])
      exact ⟨E.1,E.2.trans (by norm_num [cell12372])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy36 (n := 12372) (by norm_num)
        (q := 1 - (cell12372 ⟨36,by decide⟩).lower)
        (by norm_num [cell12372]) (by norm_num [cell12372])
      exact ⟨E.1,E.2.trans (by norm_num [cell12372])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy37 (n := 12372) (by norm_num)
        (q := 1 - (cell12372 ⟨37,by decide⟩).lower)
        (by norm_num [cell12372]) (by norm_num [cell12372])
      exact ⟨E.1,E.2.trans (by norm_num [cell12372])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy38 (n := 12372) (by norm_num)
        (q := 1 - (cell12372 ⟨38,by decide⟩).lower)
        (by norm_num [cell12372]) (by norm_num [cell12372])
      exact ⟨E.1,E.2.trans (by norm_num [cell12372])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy39 (n := 12372) (by norm_num)
        (q := 1 - (cell12372 ⟨39,by decide⟩).lower)
        (by norm_num [cell12372]) (by norm_num [cell12372])
      exact ⟨E.1,E.2.trans (by norm_num [cell12372])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy40 (n := 12372) (by norm_num)
        (q := 1 - (cell12372 ⟨40,by decide⟩).lower)
        (by norm_num [cell12372]) (by norm_num [cell12372])
      exact ⟨E.1,E.2.trans (by norm_num [cell12372])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy41 (n := 12372) (by norm_num)
        (q := 1 - (cell12372 ⟨41,by decide⟩).lower)
        (by norm_num [cell12372]) (by norm_num [cell12372])
      exact ⟨E.1,E.2.trans (by norm_num [cell12372])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy42 (n := 12372) (by norm_num)
        (q := 1 - (cell12372 ⟨42,by decide⟩).lower)
        (by norm_num [cell12372]) (by norm_num [cell12372])
      exact ⟨E.1,E.2.trans (by norm_num [cell12372])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy43 (n := 12372) (by norm_num)
        (q := 1 - (cell12372 ⟨43,by decide⟩).lower)
        (by norm_num [cell12372]) (by norm_num [cell12372])
      exact ⟨E.1,E.2.trans (by norm_num [cell12372])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy44 (n := 12372) (by norm_num)
        (q := 1 - (cell12372 ⟨44,by decide⟩).lower)
        (by norm_num [cell12372]) (by norm_num [cell12372])
      exact ⟨E.1,E.2.trans (by norm_num [cell12372])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy45 (n := 12372) (by norm_num)
        (q := 1 - (cell12372 ⟨45,by decide⟩).lower)
        (by norm_num [cell12372]) (by norm_num [cell12372])
      exact ⟨E.1,E.2.trans (by norm_num [cell12372])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy46 (n := 12372) (by norm_num)
        (q := 1 - (cell12372 ⟨46,by decide⟩).lower)
        (by norm_num [cell12372]) (by norm_num [cell12372])
      exact ⟨E.1,E.2.trans (by norm_num [cell12372])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy47 (n := 12372) (by norm_num)
        (q := 1 - (cell12372 ⟨47,by decide⟩).lower)
        (by norm_num [cell12372]) (by norm_num [cell12372])
      exact ⟨E.1,E.2.trans (by norm_num [cell12372])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy48 (n := 12372) (by norm_num)
        (q := 1 - (cell12372 ⟨48,by decide⟩).lower)
        (by norm_num [cell12372]) (by norm_num [cell12372])
      exact ⟨E.1,E.2.trans (by norm_num [cell12372])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy49 (n := 12372) (by norm_num)
        (q := 1 - (cell12372 ⟨49,by decide⟩).lower)
        (by norm_num [cell12372]) (by norm_num [cell12372])
      exact ⟨E.1,E.2.trans (by norm_num [cell12372])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy50 (n := 12372) (by norm_num)
        (q := 1 - (cell12372 ⟨50,by decide⟩).lower)
        (by norm_num [cell12372]) (by norm_num [cell12372])
      exact ⟨E.1,E.2.trans (by norm_num [cell12372])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy51 (n := 12372) (by norm_num)
        (q := 1 - (cell12372 ⟨51,by decide⟩).lower)
        (by norm_num [cell12372]) (by norm_num [cell12372])
      exact ⟨E.1,E.2.trans (by norm_num [cell12372])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy52 (n := 12372) (by norm_num)
        (q := 1 - (cell12372 ⟨52,by decide⟩).lower)
        (by norm_num [cell12372]) (by norm_num [cell12372])
      exact ⟨E.1,E.2.trans (by norm_num [cell12372])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12372

/-! Source-cell containment and simple scalar guards at 12372. -/
namespace BstLean.Part269.N12372
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12372)
open BstLean.Part268 (cell12372)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12372 ⟨10,by decide⟩).lower ∧ (cell12372 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12372 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12372 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12372 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12372 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12372 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12372,cell12372,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12372 ⟨11,by decide⟩).lower ∧ (cell12372 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12372 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12372 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12372 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12372 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12372 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12372,cell12372,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12372 ⟨12,by decide⟩).lower ∧ (cell12372 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12372 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12372 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12372 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12372 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12372 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12372,cell12372,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12372 ⟨13,by decide⟩).lower ∧ (cell12372 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12372 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12372 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12372 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12372 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12372 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12372,cell12372,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12372 ⟨14,by decide⟩).lower ∧ (cell12372 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12372 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12372 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12372 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12372 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12372 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12372,cell12372,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12372 ⟨15,by decide⟩).lower ∧ (cell12372 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12372 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12372 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12372 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12372 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12372 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12372,cell12372,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12372 ⟨16,by decide⟩).lower ∧ (cell12372 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12372 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12372 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12372 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12372 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12372 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12372,cell12372,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12372 ⟨17,by decide⟩).lower ∧ (cell12372 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12372 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12372 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12372 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12372 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12372 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12372,cell12372,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12372 ⟨18,by decide⟩).lower ∧ (cell12372 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12372 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12372 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12372 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12372 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12372 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12372,cell12372,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12372 ⟨19,by decide⟩).lower ∧ (cell12372 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12372 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12372 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12372 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12372 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12372 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12372,cell12372,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12372 ⟨20,by decide⟩).lower ∧ (cell12372 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12372 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12372 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12372 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12372 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12372 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12372,cell12372,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12372 ⟨21,by decide⟩).lower ∧ (cell12372 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12372 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12372 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12372 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12372 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12372 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12372,cell12372,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12372 ⟨22,by decide⟩).lower ∧ (cell12372 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12372 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12372 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12372 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12372 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12372 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12372,cell12372,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12372 ⟨23,by decide⟩).lower ∧ (cell12372 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12372 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12372 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12372 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12372 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12372 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12372,cell12372,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12372 ⟨24,by decide⟩).lower ∧ (cell12372 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12372 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12372 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12372 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12372 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12372 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12372,cell12372,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12372 ⟨25,by decide⟩).lower ∧ (cell12372 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12372 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12372 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12372 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12372 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12372 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12372,cell12372,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12372 ⟨26,by decide⟩).lower ∧ (cell12372 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12372 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12372 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12372 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12372 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12372 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12372,cell12372,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12372 ⟨27,by decide⟩).lower ∧ (cell12372 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12372 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12372 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12372 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12372 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12372 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12372,cell12372,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12372 ⟨28,by decide⟩).lower ∧ (cell12372 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12372 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12372 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12372 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12372 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12372 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12372,cell12372,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12372 ⟨29,by decide⟩).lower ∧ (cell12372 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12372 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12372 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12372 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12372 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12372 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12372,cell12372,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12372 ⟨30,by decide⟩).lower ∧ (cell12372 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12372 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12372 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12372 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12372 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12372 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12372,cell12372,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12372 ⟨31,by decide⟩).lower ∧ (cell12372 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12372 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12372 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12372 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12372 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12372 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12372,cell12372,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12372 ⟨32,by decide⟩).lower ∧ (cell12372 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12372 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12372 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12372 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12372 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12372 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12372,cell12372,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12372 ⟨33,by decide⟩).lower ∧ (cell12372 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12372 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12372 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12372 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12372 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12372 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12372,cell12372,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12372 ⟨34,by decide⟩).lower ∧ (cell12372 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12372 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12372 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12372 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12372 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12372 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12372,cell12372,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12372 ⟨35,by decide⟩).lower ∧ (cell12372 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12372 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12372 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12372 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12372 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12372 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12372,cell12372,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12372 ⟨36,by decide⟩).lower ∧ (cell12372 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12372 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12372 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12372 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12372 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12372 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12372,cell12372,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12372 ⟨37,by decide⟩).lower ∧ (cell12372 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12372 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12372 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12372 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12372 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12372 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12372,cell12372,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12372 ⟨38,by decide⟩).lower ∧ (cell12372 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12372 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12372 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12372 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12372 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12372 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12372,cell12372,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12372 ⟨39,by decide⟩).lower ∧ (cell12372 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12372 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12372 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12372 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12372 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12372 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12372,cell12372,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12372 ⟨40,by decide⟩).lower ∧ (cell12372 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12372 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12372 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12372 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12372 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12372 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12372,cell12372,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12372 ⟨41,by decide⟩).lower ∧ (cell12372 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12372 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12372 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12372 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12372 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12372 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12372,cell12372,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12372 ⟨42,by decide⟩).lower ∧ (cell12372 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12372 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12372 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12372 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12372 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12372 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12372,cell12372,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12372 ⟨43,by decide⟩).lower ∧ (cell12372 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12372 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12372 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12372 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12372 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12372 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12372,cell12372,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12372 ⟨44,by decide⟩).lower ∧ (cell12372 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12372 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12372 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12372 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12372 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12372 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12372,cell12372,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12372 ⟨45,by decide⟩).lower ∧ (cell12372 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12372 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12372 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12372 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12372 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12372 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12372,cell12372,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12372 ⟨46,by decide⟩).lower ∧ (cell12372 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12372 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12372 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12372 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12372 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12372 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12372,cell12372,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12372 ⟨47,by decide⟩).lower ∧ (cell12372 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12372 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12372 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12372 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12372 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12372 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12372,cell12372,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12372 ⟨48,by decide⟩).lower ∧ (cell12372 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12372 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12372 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12372 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12372 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12372 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12372,cell12372,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12372 ⟨49,by decide⟩).lower ∧ (cell12372 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12372 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12372 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12372 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12372 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12372 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12372,cell12372,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12372 ⟨50,by decide⟩).lower ∧ (cell12372 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12372 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12372 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12372 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12372 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12372 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12372,cell12372,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12372 ⟨51,by decide⟩).lower ∧ (cell12372 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12372 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12372 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12372 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12372 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12372 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12372,cell12372,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12372 ⟨52,by decide⟩).lower ∧ (cell12372 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12372 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12372 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12372 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12372 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12372 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12372,cell12372,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12372 i).lower ∧
    (cell12372 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12372 i).upper ≤ (0.532 : ℝ) ∧
    (cell12372 i).centre ≤ (0.1 : ℝ) ∧ (cell12372 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12372 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12372 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12372

/-! The local source numeric instances at 12372 have no network premises. -/
namespace BstLean.Part269.N12372
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12372)
open BstLean.Part268 (cell12372)

noncomputable def sourceNumerics12372 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12372 (cell12372 i)
      scalarRow12372.M scalarRow12372.H scalarRow12372.xi := by
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
    energy_allowance := scalarRow12372.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12372]
    centre_nonneg := (scalarRow12372.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D0.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12372])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12372
/-! Actual 12373 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12373
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12373 ≤ (1.036283516565 : ℝ) := by
  have hr : (111.233987611700 : ℝ) ≤ √(12373 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.233987611700 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12373 12373 (11 / 1000) ≤
    (0.008593480705 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12373) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.233987611700 : ℝ) ≤ √(12373 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12373)
  have hdiv : K / √(12373 : ℝ) ≤ K / 111.233987611700 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.233987611700 ≤ (0.008593480705 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12373.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12373 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12373 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12373 := gPlus_lower 12373
end BstLean.Part269.N12373

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12373
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036283516564 : ℝ) ≤ wn 12373 := by
  have hn : √(12373 : ℝ) ≤ 111.233987611701 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12373 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.233987611701 ≤ 2 / √(12373 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000258656090 : ℝ) ≤ rhoBar 12373 BstLean.Part154.csC ∧
    rhoBar 12373 BstLean.Part154.csC ≤ 0.000258656490 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036283516564 : ℝ) / (1.295212 * 12373) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036283516565 : ℝ) / (1.29521 * 12373) := by gcongr
      _ ≤ (0.000258656490 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12373 BstLean.Part154.csC) ≤ 0.001034692864 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12373 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12373 BstLean.Part154.csC) (piBar (rhoBar 12373 BstLean.Part154.csC)) ≤ 0.000197563819 ∧
    cc1 (rhoBar 12373 BstLean.Part154.csC) (piBar (rhoBar 12373 BstLean.Part154.csC)) ≤ 0.000125711119 ∧
    cc2 (rhoBar 12373 BstLean.Part154.csC) ≤ 0.000072976206 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12373 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12373 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12373 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12373 BstLean.Part154.csC * nuR (rhoBar 12373 BstLean.Part154.csC)) ≤ 0.000517329706 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000258656490 : ℝ) * 0.001034692864 := by gcongr
      _ ≤ (0.000517329706 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12373 BstLean.Part154.csC) * nuR (rhoBar 12373 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001034692864 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12373 BstLean.Part154.csC) * rhoBar 12373 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000258656490 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000258656490 / 2 + 0.399 * 0.001034692864 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000197563819 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000517329706 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125711119 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000258656490 / 1.414213562 := by gcongr
      _ ≤ (0.000072976206 : ℝ) := by norm_num

end BstLean.Part269.N12373

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12373
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12373 BstLean.Part154.csC) (piBar (rhoBar 12373 BstLean.Part154.csC)) ≤ 1.68558E-7 := by
  have hr0 : 0 ≤ rhoBar 12373 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12373 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12373 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12373 BstLean.Part154.csC) (piBar (rhoBar 12373 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12373 BstLean.Part154.csC) (piBar (rhoBar 12373 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12373 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000197563819 : ℝ) ^ 2 + 0.000125711119 ^ 2 + 3 * 0.000072976206 ^ 2 +
        2 * 0.797885 * 0.000197563819 * 0.000125711119 + 2 * 0.000197563819 * 0.000072976206 +
        4 * 0.797885 * 0.000125711119 * 0.000072976206 := by gcongr
    _ ≤ (1.68558E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12373 BstLean.Part154.csC Θ ≤ 0.002701252880 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12373 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12373 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12373 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12373 BstLean.Part154.csC) (piBar (rhoBar 12373 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12373 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036283516565 * 1.68558E-7 / (0.000258656090 : ℝ) := by gcongr
    _ ≤ 0.002701252880 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12373 BstLean.Part154.csC Θ ≤ 0.002998559320 + 0.000682562108 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12373 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12373 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12373 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036283516565 : ℝ) * ((2 * Θ * 0.000258656490 +
        (6863 / 10000) * 0.000258656490 * 12373 * 0.001034692864) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002998559320 + 0.000682562108 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12373 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12373 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12373 0.011 Θ ∧ gammaRatio 12373 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12373 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036283516565 : ℝ) * 0.525 / ((1 - 0.011) * 12373) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12373 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12373 0.011 Θ) :=
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
    badAllowance 12373 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12373 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12373 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12373 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12373 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12373 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12373 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12373 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12373 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12373 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12373 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036283516565 : ℝ) * 12373 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12373 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004098559320 + 0.003383814988 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12373

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12373
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12373 BstLean.Part154.csC) (piBar (rhoBar 12373 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12373 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12373 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12373 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12373 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12373 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12373 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12373 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12373 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12373 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12373 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12373 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12373 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12373 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12373 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053180900674 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12373) ≤ 0.010736265118 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12373 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036283516565)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010736265118 + 2 * 0.737676 / 12373) := by gcongr
    _ ≤ (0.053180900674 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12373 12 ≤ 0.0015 := by
  exact BstLean.Part269.S0.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12373

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12373
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560488389557 : ℝ) ≤ plow 12373 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12373) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053381662189)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001418157762) : eMP 12373 0.011 xi bn ≤ 0.001220494390 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12373 : ℝ) * (1 - 0.011))) ≤ 0.000603394826 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001418157762 / (12373 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000603394826 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000603394826 : ℝ) + 3.141593 * 0.053381662189 / (12373 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001220494390 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053381662189)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001418157762) : PiBarMP 12373 12 0.011 xi bn ≤ 0.163391553114 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12373 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037658435470 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.620508948386 : ℝ) ≤ √((12373 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.233987611700 : ℝ) ≤ √(12373 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12373) ≤ 0.125253158337 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037658435470 + 0.053381662189 * 1.772454 / (2 * (110.620508948386 : ℝ))) * (1 + 0.001220494390) +
        8 / (12373 * 111.233987611700) + 0.125253158337 := by gcongr
    _ ≤ (0.163391553114 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053381662189)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001418157762) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284225619699) :
    parallelOracle 12373 0.011 xi bn cd ≤ 0.164411871798 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12373 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12373 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560488389557 : ℝ) ≤ plow 12373 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.233987611700 : ℝ) ≤ √(12373 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284225619699 : ℝ) / (2 * 0.560488389557 * 111.233987611700)) * 0.163391553114 +
        0.284225619699 ^ 2 / (2 * 0.560488389557 * 111.233987611700) := by gcongr
    _ ≤ (0.164411871798 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053381662189) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001418157762)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284225619699) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12373 12373 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560488389557 : ℝ) ≤ plow 12373 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.233987611700 : ℝ) ≤ √(12373 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12373 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12373 Θ 1.22 ≤ 0.011921720407 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.233987611700 := by gcongr <;> linarith
      _ ≤ (0.011921720407 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12373 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12373 12373 0.011 ≤ 0.008593480705 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12373 12373 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12373 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12373 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12373 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12373 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164411871798 + 0.011921720407 + (0.008593480705 : ℝ) *
        (1 + 2 * (0.284225619699 + 0.011921720407) / (0.560488389557 * 111.233987611700))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12373]

end BstLean.Part269.N12373

/-! The original eight local profiles supply actual 12373 moment certificates. -/
namespace BstLean.Part269.N12373
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12373 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12373 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12373 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053381662189 ∧
    0 ≤ bN 12373 BstLean.Part154.csC (groupTheta g) ∧ bN 12373 BstLean.Part154.csC (groupTheta g) ≤ 0.001418157762 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12373 12373 0.011
      (momentAllowance 12373 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12373 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12373 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12373 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12373 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12373 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231044719025 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12373 0.011
      (momentAllowance 12373 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12373 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12373
/-! The actual computed-centre upper energy formula at 12373. -/
namespace BstLean.Part269.N12373
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12373

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12373
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12373)
open BstLean.Part268 (cell12373)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086508973763
  | 2 => 0.087471999035
  | 3 => 0.088436365659
  | 4 => 0.089404209723
  | 5 => 0.090378087836
  | 6 => 0.091361035946
  | 7 => 0.092356633060
  | 8 => 0.093369069771
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12373 12373 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12373 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12373

/-! Actual upper energy certificates on all 43 source endpoints at 12373. -/
namespace BstLean.Part269.N12373
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12373)
open BstLean.Part268 (cell12373)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12373 (gMinus 12373) (1 - (cell12373 i).lower) ≤ 1 ∧
    energyUpper 12373 (gMinus 12373) (BstLean.Part211.gPlus 12373)
      (finiteEnergy 12373 12373 0.011) (1 - (cell12373 i).lower) ≤
      (cell12373 i).energy := by
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
      have E := BstLean.Part269.S0.uniformEnergy10 (n := 12373) (by norm_num)
        (q := 1 - (cell12373 ⟨10,by decide⟩).lower)
        (by norm_num [cell12373]) (by norm_num [cell12373])
      exact ⟨E.1,E.2.trans (by norm_num [cell12373])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy11 (n := 12373) (by norm_num)
        (q := 1 - (cell12373 ⟨11,by decide⟩).lower)
        (by norm_num [cell12373]) (by norm_num [cell12373])
      exact ⟨E.1,E.2.trans (by norm_num [cell12373])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy12 (n := 12373) (by norm_num)
        (q := 1 - (cell12373 ⟨12,by decide⟩).lower)
        (by norm_num [cell12373]) (by norm_num [cell12373])
      exact ⟨E.1,E.2.trans (by norm_num [cell12373])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy13 (n := 12373) (by norm_num)
        (q := 1 - (cell12373 ⟨13,by decide⟩).lower)
        (by norm_num [cell12373]) (by norm_num [cell12373])
      exact ⟨E.1,E.2.trans (by norm_num [cell12373])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy14 (n := 12373) (by norm_num)
        (q := 1 - (cell12373 ⟨14,by decide⟩).lower)
        (by norm_num [cell12373]) (by norm_num [cell12373])
      exact ⟨E.1,E.2.trans (by norm_num [cell12373])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy15 (n := 12373) (by norm_num)
        (q := 1 - (cell12373 ⟨15,by decide⟩).lower)
        (by norm_num [cell12373]) (by norm_num [cell12373])
      exact ⟨E.1,E.2.trans (by norm_num [cell12373])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy16 (n := 12373) (by norm_num)
        (q := 1 - (cell12373 ⟨16,by decide⟩).lower)
        (by norm_num [cell12373]) (by norm_num [cell12373])
      exact ⟨E.1,E.2.trans (by norm_num [cell12373])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy17 (n := 12373) (by norm_num)
        (q := 1 - (cell12373 ⟨17,by decide⟩).lower)
        (by norm_num [cell12373]) (by norm_num [cell12373])
      exact ⟨E.1,E.2.trans (by norm_num [cell12373])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy18 (n := 12373) (by norm_num)
        (q := 1 - (cell12373 ⟨18,by decide⟩).lower)
        (by norm_num [cell12373]) (by norm_num [cell12373])
      exact ⟨E.1,E.2.trans (by norm_num [cell12373])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy19 (n := 12373) (by norm_num)
        (q := 1 - (cell12373 ⟨19,by decide⟩).lower)
        (by norm_num [cell12373]) (by norm_num [cell12373])
      exact ⟨E.1,E.2.trans (by norm_num [cell12373])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy20 (n := 12373) (by norm_num)
        (q := 1 - (cell12373 ⟨20,by decide⟩).lower)
        (by norm_num [cell12373]) (by norm_num [cell12373])
      exact ⟨E.1,E.2.trans (by norm_num [cell12373])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy21 (n := 12373) (by norm_num)
        (q := 1 - (cell12373 ⟨21,by decide⟩).lower)
        (by norm_num [cell12373]) (by norm_num [cell12373])
      exact ⟨E.1,E.2.trans (by norm_num [cell12373])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy22 (n := 12373) (by norm_num)
        (q := 1 - (cell12373 ⟨22,by decide⟩).lower)
        (by norm_num [cell12373]) (by norm_num [cell12373])
      exact ⟨E.1,E.2.trans (by norm_num [cell12373])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy23 (n := 12373) (by norm_num)
        (q := 1 - (cell12373 ⟨23,by decide⟩).lower)
        (by norm_num [cell12373]) (by norm_num [cell12373])
      exact ⟨E.1,E.2.trans (by norm_num [cell12373])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy24 (n := 12373) (by norm_num)
        (q := 1 - (cell12373 ⟨24,by decide⟩).lower)
        (by norm_num [cell12373]) (by norm_num [cell12373])
      exact ⟨E.1,E.2.trans (by norm_num [cell12373])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy25 (n := 12373) (by norm_num)
        (q := 1 - (cell12373 ⟨25,by decide⟩).lower)
        (by norm_num [cell12373]) (by norm_num [cell12373])
      exact ⟨E.1,E.2.trans (by norm_num [cell12373])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy26 (n := 12373) (by norm_num)
        (q := 1 - (cell12373 ⟨26,by decide⟩).lower)
        (by norm_num [cell12373]) (by norm_num [cell12373])
      exact ⟨E.1,E.2.trans (by norm_num [cell12373])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy27 (n := 12373) (by norm_num)
        (q := 1 - (cell12373 ⟨27,by decide⟩).lower)
        (by norm_num [cell12373]) (by norm_num [cell12373])
      exact ⟨E.1,E.2.trans (by norm_num [cell12373])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy28 (n := 12373) (by norm_num)
        (q := 1 - (cell12373 ⟨28,by decide⟩).lower)
        (by norm_num [cell12373]) (by norm_num [cell12373])
      exact ⟨E.1,E.2.trans (by norm_num [cell12373])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy29 (n := 12373) (by norm_num)
        (q := 1 - (cell12373 ⟨29,by decide⟩).lower)
        (by norm_num [cell12373]) (by norm_num [cell12373])
      exact ⟨E.1,E.2.trans (by norm_num [cell12373])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy30 (n := 12373) (by norm_num)
        (q := 1 - (cell12373 ⟨30,by decide⟩).lower)
        (by norm_num [cell12373]) (by norm_num [cell12373])
      exact ⟨E.1,E.2.trans (by norm_num [cell12373])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy31 (n := 12373) (by norm_num)
        (q := 1 - (cell12373 ⟨31,by decide⟩).lower)
        (by norm_num [cell12373]) (by norm_num [cell12373])
      exact ⟨E.1,E.2.trans (by norm_num [cell12373])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy32 (n := 12373) (by norm_num)
        (q := 1 - (cell12373 ⟨32,by decide⟩).lower)
        (by norm_num [cell12373]) (by norm_num [cell12373])
      exact ⟨E.1,E.2.trans (by norm_num [cell12373])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy33 (n := 12373) (by norm_num)
        (q := 1 - (cell12373 ⟨33,by decide⟩).lower)
        (by norm_num [cell12373]) (by norm_num [cell12373])
      exact ⟨E.1,E.2.trans (by norm_num [cell12373])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy34 (n := 12373) (by norm_num)
        (q := 1 - (cell12373 ⟨34,by decide⟩).lower)
        (by norm_num [cell12373]) (by norm_num [cell12373])
      exact ⟨E.1,E.2.trans (by norm_num [cell12373])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy35 (n := 12373) (by norm_num)
        (q := 1 - (cell12373 ⟨35,by decide⟩).lower)
        (by norm_num [cell12373]) (by norm_num [cell12373])
      exact ⟨E.1,E.2.trans (by norm_num [cell12373])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy36 (n := 12373) (by norm_num)
        (q := 1 - (cell12373 ⟨36,by decide⟩).lower)
        (by norm_num [cell12373]) (by norm_num [cell12373])
      exact ⟨E.1,E.2.trans (by norm_num [cell12373])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy37 (n := 12373) (by norm_num)
        (q := 1 - (cell12373 ⟨37,by decide⟩).lower)
        (by norm_num [cell12373]) (by norm_num [cell12373])
      exact ⟨E.1,E.2.trans (by norm_num [cell12373])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy38 (n := 12373) (by norm_num)
        (q := 1 - (cell12373 ⟨38,by decide⟩).lower)
        (by norm_num [cell12373]) (by norm_num [cell12373])
      exact ⟨E.1,E.2.trans (by norm_num [cell12373])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy39 (n := 12373) (by norm_num)
        (q := 1 - (cell12373 ⟨39,by decide⟩).lower)
        (by norm_num [cell12373]) (by norm_num [cell12373])
      exact ⟨E.1,E.2.trans (by norm_num [cell12373])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy40 (n := 12373) (by norm_num)
        (q := 1 - (cell12373 ⟨40,by decide⟩).lower)
        (by norm_num [cell12373]) (by norm_num [cell12373])
      exact ⟨E.1,E.2.trans (by norm_num [cell12373])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy41 (n := 12373) (by norm_num)
        (q := 1 - (cell12373 ⟨41,by decide⟩).lower)
        (by norm_num [cell12373]) (by norm_num [cell12373])
      exact ⟨E.1,E.2.trans (by norm_num [cell12373])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy42 (n := 12373) (by norm_num)
        (q := 1 - (cell12373 ⟨42,by decide⟩).lower)
        (by norm_num [cell12373]) (by norm_num [cell12373])
      exact ⟨E.1,E.2.trans (by norm_num [cell12373])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy43 (n := 12373) (by norm_num)
        (q := 1 - (cell12373 ⟨43,by decide⟩).lower)
        (by norm_num [cell12373]) (by norm_num [cell12373])
      exact ⟨E.1,E.2.trans (by norm_num [cell12373])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy44 (n := 12373) (by norm_num)
        (q := 1 - (cell12373 ⟨44,by decide⟩).lower)
        (by norm_num [cell12373]) (by norm_num [cell12373])
      exact ⟨E.1,E.2.trans (by norm_num [cell12373])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy45 (n := 12373) (by norm_num)
        (q := 1 - (cell12373 ⟨45,by decide⟩).lower)
        (by norm_num [cell12373]) (by norm_num [cell12373])
      exact ⟨E.1,E.2.trans (by norm_num [cell12373])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy46 (n := 12373) (by norm_num)
        (q := 1 - (cell12373 ⟨46,by decide⟩).lower)
        (by norm_num [cell12373]) (by norm_num [cell12373])
      exact ⟨E.1,E.2.trans (by norm_num [cell12373])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy47 (n := 12373) (by norm_num)
        (q := 1 - (cell12373 ⟨47,by decide⟩).lower)
        (by norm_num [cell12373]) (by norm_num [cell12373])
      exact ⟨E.1,E.2.trans (by norm_num [cell12373])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy48 (n := 12373) (by norm_num)
        (q := 1 - (cell12373 ⟨48,by decide⟩).lower)
        (by norm_num [cell12373]) (by norm_num [cell12373])
      exact ⟨E.1,E.2.trans (by norm_num [cell12373])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy49 (n := 12373) (by norm_num)
        (q := 1 - (cell12373 ⟨49,by decide⟩).lower)
        (by norm_num [cell12373]) (by norm_num [cell12373])
      exact ⟨E.1,E.2.trans (by norm_num [cell12373])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy50 (n := 12373) (by norm_num)
        (q := 1 - (cell12373 ⟨50,by decide⟩).lower)
        (by norm_num [cell12373]) (by norm_num [cell12373])
      exact ⟨E.1,E.2.trans (by norm_num [cell12373])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy51 (n := 12373) (by norm_num)
        (q := 1 - (cell12373 ⟨51,by decide⟩).lower)
        (by norm_num [cell12373]) (by norm_num [cell12373])
      exact ⟨E.1,E.2.trans (by norm_num [cell12373])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy52 (n := 12373) (by norm_num)
        (q := 1 - (cell12373 ⟨52,by decide⟩).lower)
        (by norm_num [cell12373]) (by norm_num [cell12373])
      exact ⟨E.1,E.2.trans (by norm_num [cell12373])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12373

/-! Source-cell containment and simple scalar guards at 12373. -/
namespace BstLean.Part269.N12373
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12373)
open BstLean.Part268 (cell12373)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12373 ⟨10,by decide⟩).lower ∧ (cell12373 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12373 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12373 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12373 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12373 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12373 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12373,cell12373,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12373 ⟨11,by decide⟩).lower ∧ (cell12373 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12373 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12373 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12373 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12373 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12373 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12373,cell12373,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12373 ⟨12,by decide⟩).lower ∧ (cell12373 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12373 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12373 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12373 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12373 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12373 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12373,cell12373,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12373 ⟨13,by decide⟩).lower ∧ (cell12373 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12373 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12373 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12373 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12373 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12373 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12373,cell12373,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12373 ⟨14,by decide⟩).lower ∧ (cell12373 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12373 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12373 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12373 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12373 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12373 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12373,cell12373,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12373 ⟨15,by decide⟩).lower ∧ (cell12373 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12373 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12373 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12373 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12373 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12373 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12373,cell12373,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12373 ⟨16,by decide⟩).lower ∧ (cell12373 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12373 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12373 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12373 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12373 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12373 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12373,cell12373,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12373 ⟨17,by decide⟩).lower ∧ (cell12373 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12373 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12373 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12373 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12373 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12373 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12373,cell12373,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12373 ⟨18,by decide⟩).lower ∧ (cell12373 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12373 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12373 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12373 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12373 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12373 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12373,cell12373,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12373 ⟨19,by decide⟩).lower ∧ (cell12373 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12373 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12373 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12373 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12373 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12373 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12373,cell12373,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12373 ⟨20,by decide⟩).lower ∧ (cell12373 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12373 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12373 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12373 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12373 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12373 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12373,cell12373,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12373 ⟨21,by decide⟩).lower ∧ (cell12373 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12373 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12373 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12373 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12373 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12373 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12373,cell12373,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12373 ⟨22,by decide⟩).lower ∧ (cell12373 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12373 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12373 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12373 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12373 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12373 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12373,cell12373,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12373 ⟨23,by decide⟩).lower ∧ (cell12373 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12373 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12373 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12373 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12373 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12373 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12373,cell12373,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12373 ⟨24,by decide⟩).lower ∧ (cell12373 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12373 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12373 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12373 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12373 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12373 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12373,cell12373,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12373 ⟨25,by decide⟩).lower ∧ (cell12373 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12373 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12373 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12373 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12373 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12373 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12373,cell12373,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12373 ⟨26,by decide⟩).lower ∧ (cell12373 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12373 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12373 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12373 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12373 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12373 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12373,cell12373,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12373 ⟨27,by decide⟩).lower ∧ (cell12373 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12373 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12373 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12373 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12373 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12373 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12373,cell12373,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12373 ⟨28,by decide⟩).lower ∧ (cell12373 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12373 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12373 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12373 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12373 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12373 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12373,cell12373,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12373 ⟨29,by decide⟩).lower ∧ (cell12373 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12373 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12373 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12373 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12373 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12373 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12373,cell12373,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12373 ⟨30,by decide⟩).lower ∧ (cell12373 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12373 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12373 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12373 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12373 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12373 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12373,cell12373,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12373 ⟨31,by decide⟩).lower ∧ (cell12373 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12373 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12373 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12373 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12373 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12373 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12373,cell12373,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12373 ⟨32,by decide⟩).lower ∧ (cell12373 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12373 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12373 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12373 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12373 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12373 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12373,cell12373,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12373 ⟨33,by decide⟩).lower ∧ (cell12373 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12373 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12373 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12373 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12373 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12373 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12373,cell12373,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12373 ⟨34,by decide⟩).lower ∧ (cell12373 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12373 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12373 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12373 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12373 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12373 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12373,cell12373,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12373 ⟨35,by decide⟩).lower ∧ (cell12373 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12373 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12373 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12373 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12373 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12373 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12373,cell12373,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12373 ⟨36,by decide⟩).lower ∧ (cell12373 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12373 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12373 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12373 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12373 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12373 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12373,cell12373,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12373 ⟨37,by decide⟩).lower ∧ (cell12373 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12373 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12373 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12373 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12373 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12373 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12373,cell12373,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12373 ⟨38,by decide⟩).lower ∧ (cell12373 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12373 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12373 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12373 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12373 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12373 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12373,cell12373,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12373 ⟨39,by decide⟩).lower ∧ (cell12373 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12373 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12373 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12373 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12373 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12373 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12373,cell12373,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12373 ⟨40,by decide⟩).lower ∧ (cell12373 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12373 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12373 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12373 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12373 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12373 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12373,cell12373,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12373 ⟨41,by decide⟩).lower ∧ (cell12373 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12373 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12373 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12373 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12373 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12373 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12373,cell12373,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12373 ⟨42,by decide⟩).lower ∧ (cell12373 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12373 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12373 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12373 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12373 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12373 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12373,cell12373,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12373 ⟨43,by decide⟩).lower ∧ (cell12373 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12373 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12373 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12373 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12373 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12373 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12373,cell12373,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12373 ⟨44,by decide⟩).lower ∧ (cell12373 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12373 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12373 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12373 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12373 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12373 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12373,cell12373,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12373 ⟨45,by decide⟩).lower ∧ (cell12373 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12373 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12373 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12373 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12373 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12373 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12373,cell12373,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12373 ⟨46,by decide⟩).lower ∧ (cell12373 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12373 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12373 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12373 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12373 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12373 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12373,cell12373,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12373 ⟨47,by decide⟩).lower ∧ (cell12373 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12373 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12373 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12373 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12373 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12373 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12373,cell12373,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12373 ⟨48,by decide⟩).lower ∧ (cell12373 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12373 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12373 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12373 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12373 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12373 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12373,cell12373,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12373 ⟨49,by decide⟩).lower ∧ (cell12373 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12373 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12373 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12373 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12373 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12373 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12373,cell12373,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12373 ⟨50,by decide⟩).lower ∧ (cell12373 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12373 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12373 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12373 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12373 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12373 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12373,cell12373,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12373 ⟨51,by decide⟩).lower ∧ (cell12373 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12373 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12373 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12373 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12373 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12373 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12373,cell12373,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12373 ⟨52,by decide⟩).lower ∧ (cell12373 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12373 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12373 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12373 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12373 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12373 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12373,cell12373,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12373 i).lower ∧
    (cell12373 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12373 i).upper ≤ (0.532 : ℝ) ∧
    (cell12373 i).centre ≤ (0.1 : ℝ) ∧ (cell12373 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12373 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12373 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12373

/-! The local source numeric instances at 12373 have no network premises. -/
namespace BstLean.Part269.N12373
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12373)
open BstLean.Part268 (cell12373)

noncomputable def sourceNumerics12373 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12373 (cell12373 i)
      scalarRow12373.M scalarRow12373.H scalarRow12373.xi := by
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
    energy_allowance := scalarRow12373.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12373]
    centre_nonneg := (scalarRow12373.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D0.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12373])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12373
/-! Actual 12374 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12374
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12374 ≤ (1.036282037353 : ℝ) := by
  have hr : (111.238482549880 : ℝ) ≤ √(12374 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.238482549880 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12374 12374 (11 / 1000) ≤
    (0.008593133455 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12374) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.238482549880 : ℝ) ≤ √(12374 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12374)
  have hdiv : K / √(12374 : ℝ) ≤ K / 111.238482549880 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.238482549880 ≤ (0.008593133455 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12374.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12374 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12374 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12374 := gPlus_lower 12374
end BstLean.Part269.N12374

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12374
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036282037352 : ℝ) ≤ wn 12374 := by
  have hn : √(12374 : ℝ) ≤ 111.238482549881 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12374 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.238482549881 ≤ 2 / √(12374 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000258634818 : ℝ) ≤ rhoBar 12374 BstLean.Part154.csC ∧
    rhoBar 12374 BstLean.Part154.csC ≤ 0.000258635218 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036282037352 : ℝ) / (1.295212 * 12374) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036282037353 : ℝ) / (1.29521 * 12374) := by gcongr
      _ ≤ (0.000258635218 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12374 BstLean.Part154.csC) ≤ 0.001034607765 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12374 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12374 BstLean.Part154.csC) (piBar (rhoBar 12374 BstLean.Part154.csC)) ≤ 0.000197547571 ∧
    cc1 (rhoBar 12374 BstLean.Part154.csC) (piBar (rhoBar 12374 BstLean.Part154.csC)) ≤ 0.000125700780 ∧
    cc2 (rhoBar 12374 BstLean.Part154.csC) ≤ 0.000072970204 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12374 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12374 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12374 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12374 BstLean.Part154.csC * nuR (rhoBar 12374 BstLean.Part154.csC)) ≤ 0.000517287159 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000258635218 : ℝ) * 0.001034607765 := by gcongr
      _ ≤ (0.000517287159 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12374 BstLean.Part154.csC) * nuR (rhoBar 12374 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001034607765 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12374 BstLean.Part154.csC) * rhoBar 12374 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000258635218 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000258635218 / 2 + 0.399 * 0.001034607765 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000197547571 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000517287159 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125700780 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000258635218 / 1.414213562 := by gcongr
      _ ≤ (0.000072970204 : ℝ) := by norm_num

end BstLean.Part269.N12374

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12374
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12374 BstLean.Part154.csC) (piBar (rhoBar 12374 BstLean.Part154.csC)) ≤ 1.68530E-7 := by
  have hr0 : 0 ≤ rhoBar 12374 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12374 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12374 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12374 BstLean.Part154.csC) (piBar (rhoBar 12374 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12374 BstLean.Part154.csC) (piBar (rhoBar 12374 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12374 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000197547571 : ℝ) ^ 2 + 0.000125700780 ^ 2 + 3 * 0.000072970204 ^ 2 +
        2 * 0.797885 * 0.000197547571 * 0.000125700780 + 2 * 0.000197547571 * 0.000072970204 +
        4 * 0.797885 * 0.000125700780 * 0.000072970204 := by gcongr
    _ ≤ (1.68530E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12374 BstLean.Part154.csC Θ ≤ 0.002701022440 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12374 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12374 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12374 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12374 BstLean.Part154.csC) (piBar (rhoBar 12374 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12374 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036282037353 * 1.68530E-7 / (0.000258634818 : ℝ) := by gcongr
    _ ≤ 0.002701022440 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12374 BstLean.Part154.csC Θ ≤ 0.002998304146 + 0.000682505000 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12374 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12374 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12374 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036282037353 : ℝ) * ((2 * Θ * 0.000258635218 +
        (6863 / 10000) * 0.000258635218 * 12374 * 0.001034607765) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002998304146 + 0.000682505000 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12374 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12374 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12374 0.011 Θ ∧ gammaRatio 12374 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12374 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036282037353 : ℝ) * 0.525 / ((1 - 0.011) * 12374) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12374 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12374 0.011 Θ) :=
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
    badAllowance 12374 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12374 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12374 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12374 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12374 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12374 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12374 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12374 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12374 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12374 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12374 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036282037353 : ℝ) * 12374 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12374 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004098304146 + 0.003383527440 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12374

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12374
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12374 BstLean.Part154.csC) (piBar (rhoBar 12374 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12374 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12374 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12374 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12374 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12374 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12374 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12374 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12374 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12374 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12374 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12374 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12374 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12374 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12374 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053178728127 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12374) ≤ 0.010735831285 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12374 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036282037353)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010735831285 + 2 * 0.737676 / 12374) := by gcongr
    _ ≤ (0.053178728127 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12374 12 ≤ 0.0015 := by
  exact BstLean.Part269.S0.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12374

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12374
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560488437198 : ℝ) ≤ plow 12374 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12374) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053381256052)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001418036781) : eMP 12374 0.011 xi bn ≤ 0.001220392940 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12374 : ℝ) * (1 - 0.011))) ≤ 0.000603344707 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001418036781 / (12374 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000603344707 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000603344707 : ℝ) + 3.141593 * 0.053381256052 / (12374 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001220392940 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053381256052)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001418036781) : PiBarMP 12374 12 0.011 xi bn ≤ 0.163384858453 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12374 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037656829142 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.624979096043 : ℝ) ≤ √((12374 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.238482549880 : ℝ) ≤ √(12374 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12374) ≤ 0.125248097092 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037656829142 + 0.053381256052 * 1.772454 / (2 * (110.624979096043 : ℝ))) * (1 + 0.001220392940) +
        8 / (12374 * 111.238482549880) + 0.125248097092 := by gcongr
    _ ≤ (0.163384858453 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053381256052)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001418036781) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284222568236) :
    parallelOracle 12374 0.011 xi bn cd ≤ 0.164405102652 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12374 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12374 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560488437198 : ℝ) ≤ plow 12374 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.238482549880 : ℝ) ≤ √(12374 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284222568236 : ℝ) / (2 * 0.560488437198 * 111.238482549880)) * 0.163384858453 +
        0.284222568236 ^ 2 / (2 * 0.560488437198 * 111.238482549880) := by gcongr
    _ ≤ (0.164405102652 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053381256052) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001418036781)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284222568236) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12374 12374 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560488437198 : ℝ) ≤ plow 12374 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.238482549880 : ℝ) ≤ √(12374 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12374 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12374 Θ 1.22 ≤ 0.011921238673 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.238482549880 := by gcongr <;> linarith
      _ ≤ (0.011921238673 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12374 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12374 12374 0.011 ≤ 0.008593133455 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12374 12374 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12374 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12374 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12374 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12374 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164405102652 + 0.011921238673 + (0.008593133455 : ℝ) *
        (1 + 2 * (0.284222568236 + 0.011921238673) / (0.560488437198 * 111.238482549880))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12374]

end BstLean.Part269.N12374

/-! The original eight local profiles supply actual 12374 moment certificates. -/
namespace BstLean.Part269.N12374
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12374 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12374 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12374 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053381256052 ∧
    0 ≤ bN 12374 BstLean.Part154.csC (groupTheta g) ∧ bN 12374 BstLean.Part154.csC (groupTheta g) ≤ 0.001418036781 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12374 12374 0.011
      (momentAllowance 12374 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12374 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12374 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12374 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12374 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12374 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231043840109 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12374 0.011
      (momentAllowance 12374 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12374 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12374
/-! The actual computed-centre upper energy formula at 12374. -/
namespace BstLean.Part269.N12374
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12374

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12374
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12374)
open BstLean.Part268 (cell12374)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086505635841
  | 2 => 0.087468589424
  | 3 => 0.088432872305
  | 4 => 0.089400617934
  | 5 => 0.090374379832
  | 6 => 0.091357190371
  | 7 => 0.092352624435
  | 8 => 0.093364867892
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12374 12374 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12374 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12374

/-! Actual upper energy certificates on all 43 source endpoints at 12374. -/
namespace BstLean.Part269.N12374
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12374)
open BstLean.Part268 (cell12374)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12374 (gMinus 12374) (1 - (cell12374 i).lower) ≤ 1 ∧
    energyUpper 12374 (gMinus 12374) (BstLean.Part211.gPlus 12374)
      (finiteEnergy 12374 12374 0.011) (1 - (cell12374 i).lower) ≤
      (cell12374 i).energy := by
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
      have E := BstLean.Part269.S0.uniformEnergy10 (n := 12374) (by norm_num)
        (q := 1 - (cell12374 ⟨10,by decide⟩).lower)
        (by norm_num [cell12374]) (by norm_num [cell12374])
      exact ⟨E.1,E.2.trans (by norm_num [cell12374])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy11 (n := 12374) (by norm_num)
        (q := 1 - (cell12374 ⟨11,by decide⟩).lower)
        (by norm_num [cell12374]) (by norm_num [cell12374])
      exact ⟨E.1,E.2.trans (by norm_num [cell12374])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy12 (n := 12374) (by norm_num)
        (q := 1 - (cell12374 ⟨12,by decide⟩).lower)
        (by norm_num [cell12374]) (by norm_num [cell12374])
      exact ⟨E.1,E.2.trans (by norm_num [cell12374])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy13 (n := 12374) (by norm_num)
        (q := 1 - (cell12374 ⟨13,by decide⟩).lower)
        (by norm_num [cell12374]) (by norm_num [cell12374])
      exact ⟨E.1,E.2.trans (by norm_num [cell12374])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy14 (n := 12374) (by norm_num)
        (q := 1 - (cell12374 ⟨14,by decide⟩).lower)
        (by norm_num [cell12374]) (by norm_num [cell12374])
      exact ⟨E.1,E.2.trans (by norm_num [cell12374])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy15 (n := 12374) (by norm_num)
        (q := 1 - (cell12374 ⟨15,by decide⟩).lower)
        (by norm_num [cell12374]) (by norm_num [cell12374])
      exact ⟨E.1,E.2.trans (by norm_num [cell12374])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy16 (n := 12374) (by norm_num)
        (q := 1 - (cell12374 ⟨16,by decide⟩).lower)
        (by norm_num [cell12374]) (by norm_num [cell12374])
      exact ⟨E.1,E.2.trans (by norm_num [cell12374])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy17 (n := 12374) (by norm_num)
        (q := 1 - (cell12374 ⟨17,by decide⟩).lower)
        (by norm_num [cell12374]) (by norm_num [cell12374])
      exact ⟨E.1,E.2.trans (by norm_num [cell12374])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy18 (n := 12374) (by norm_num)
        (q := 1 - (cell12374 ⟨18,by decide⟩).lower)
        (by norm_num [cell12374]) (by norm_num [cell12374])
      exact ⟨E.1,E.2.trans (by norm_num [cell12374])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy19 (n := 12374) (by norm_num)
        (q := 1 - (cell12374 ⟨19,by decide⟩).lower)
        (by norm_num [cell12374]) (by norm_num [cell12374])
      exact ⟨E.1,E.2.trans (by norm_num [cell12374])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy20 (n := 12374) (by norm_num)
        (q := 1 - (cell12374 ⟨20,by decide⟩).lower)
        (by norm_num [cell12374]) (by norm_num [cell12374])
      exact ⟨E.1,E.2.trans (by norm_num [cell12374])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy21 (n := 12374) (by norm_num)
        (q := 1 - (cell12374 ⟨21,by decide⟩).lower)
        (by norm_num [cell12374]) (by norm_num [cell12374])
      exact ⟨E.1,E.2.trans (by norm_num [cell12374])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy22 (n := 12374) (by norm_num)
        (q := 1 - (cell12374 ⟨22,by decide⟩).lower)
        (by norm_num [cell12374]) (by norm_num [cell12374])
      exact ⟨E.1,E.2.trans (by norm_num [cell12374])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy23 (n := 12374) (by norm_num)
        (q := 1 - (cell12374 ⟨23,by decide⟩).lower)
        (by norm_num [cell12374]) (by norm_num [cell12374])
      exact ⟨E.1,E.2.trans (by norm_num [cell12374])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy24 (n := 12374) (by norm_num)
        (q := 1 - (cell12374 ⟨24,by decide⟩).lower)
        (by norm_num [cell12374]) (by norm_num [cell12374])
      exact ⟨E.1,E.2.trans (by norm_num [cell12374])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy25 (n := 12374) (by norm_num)
        (q := 1 - (cell12374 ⟨25,by decide⟩).lower)
        (by norm_num [cell12374]) (by norm_num [cell12374])
      exact ⟨E.1,E.2.trans (by norm_num [cell12374])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy26 (n := 12374) (by norm_num)
        (q := 1 - (cell12374 ⟨26,by decide⟩).lower)
        (by norm_num [cell12374]) (by norm_num [cell12374])
      exact ⟨E.1,E.2.trans (by norm_num [cell12374])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy27 (n := 12374) (by norm_num)
        (q := 1 - (cell12374 ⟨27,by decide⟩).lower)
        (by norm_num [cell12374]) (by norm_num [cell12374])
      exact ⟨E.1,E.2.trans (by norm_num [cell12374])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy28 (n := 12374) (by norm_num)
        (q := 1 - (cell12374 ⟨28,by decide⟩).lower)
        (by norm_num [cell12374]) (by norm_num [cell12374])
      exact ⟨E.1,E.2.trans (by norm_num [cell12374])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy29 (n := 12374) (by norm_num)
        (q := 1 - (cell12374 ⟨29,by decide⟩).lower)
        (by norm_num [cell12374]) (by norm_num [cell12374])
      exact ⟨E.1,E.2.trans (by norm_num [cell12374])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy30 (n := 12374) (by norm_num)
        (q := 1 - (cell12374 ⟨30,by decide⟩).lower)
        (by norm_num [cell12374]) (by norm_num [cell12374])
      exact ⟨E.1,E.2.trans (by norm_num [cell12374])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy31 (n := 12374) (by norm_num)
        (q := 1 - (cell12374 ⟨31,by decide⟩).lower)
        (by norm_num [cell12374]) (by norm_num [cell12374])
      exact ⟨E.1,E.2.trans (by norm_num [cell12374])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy32 (n := 12374) (by norm_num)
        (q := 1 - (cell12374 ⟨32,by decide⟩).lower)
        (by norm_num [cell12374]) (by norm_num [cell12374])
      exact ⟨E.1,E.2.trans (by norm_num [cell12374])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy33 (n := 12374) (by norm_num)
        (q := 1 - (cell12374 ⟨33,by decide⟩).lower)
        (by norm_num [cell12374]) (by norm_num [cell12374])
      exact ⟨E.1,E.2.trans (by norm_num [cell12374])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy34 (n := 12374) (by norm_num)
        (q := 1 - (cell12374 ⟨34,by decide⟩).lower)
        (by norm_num [cell12374]) (by norm_num [cell12374])
      exact ⟨E.1,E.2.trans (by norm_num [cell12374])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy35 (n := 12374) (by norm_num)
        (q := 1 - (cell12374 ⟨35,by decide⟩).lower)
        (by norm_num [cell12374]) (by norm_num [cell12374])
      exact ⟨E.1,E.2.trans (by norm_num [cell12374])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy36 (n := 12374) (by norm_num)
        (q := 1 - (cell12374 ⟨36,by decide⟩).lower)
        (by norm_num [cell12374]) (by norm_num [cell12374])
      exact ⟨E.1,E.2.trans (by norm_num [cell12374])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy37 (n := 12374) (by norm_num)
        (q := 1 - (cell12374 ⟨37,by decide⟩).lower)
        (by norm_num [cell12374]) (by norm_num [cell12374])
      exact ⟨E.1,E.2.trans (by norm_num [cell12374])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy38 (n := 12374) (by norm_num)
        (q := 1 - (cell12374 ⟨38,by decide⟩).lower)
        (by norm_num [cell12374]) (by norm_num [cell12374])
      exact ⟨E.1,E.2.trans (by norm_num [cell12374])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy39 (n := 12374) (by norm_num)
        (q := 1 - (cell12374 ⟨39,by decide⟩).lower)
        (by norm_num [cell12374]) (by norm_num [cell12374])
      exact ⟨E.1,E.2.trans (by norm_num [cell12374])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy40 (n := 12374) (by norm_num)
        (q := 1 - (cell12374 ⟨40,by decide⟩).lower)
        (by norm_num [cell12374]) (by norm_num [cell12374])
      exact ⟨E.1,E.2.trans (by norm_num [cell12374])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy41 (n := 12374) (by norm_num)
        (q := 1 - (cell12374 ⟨41,by decide⟩).lower)
        (by norm_num [cell12374]) (by norm_num [cell12374])
      exact ⟨E.1,E.2.trans (by norm_num [cell12374])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy42 (n := 12374) (by norm_num)
        (q := 1 - (cell12374 ⟨42,by decide⟩).lower)
        (by norm_num [cell12374]) (by norm_num [cell12374])
      exact ⟨E.1,E.2.trans (by norm_num [cell12374])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy43 (n := 12374) (by norm_num)
        (q := 1 - (cell12374 ⟨43,by decide⟩).lower)
        (by norm_num [cell12374]) (by norm_num [cell12374])
      exact ⟨E.1,E.2.trans (by norm_num [cell12374])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy44 (n := 12374) (by norm_num)
        (q := 1 - (cell12374 ⟨44,by decide⟩).lower)
        (by norm_num [cell12374]) (by norm_num [cell12374])
      exact ⟨E.1,E.2.trans (by norm_num [cell12374])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy45 (n := 12374) (by norm_num)
        (q := 1 - (cell12374 ⟨45,by decide⟩).lower)
        (by norm_num [cell12374]) (by norm_num [cell12374])
      exact ⟨E.1,E.2.trans (by norm_num [cell12374])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy46 (n := 12374) (by norm_num)
        (q := 1 - (cell12374 ⟨46,by decide⟩).lower)
        (by norm_num [cell12374]) (by norm_num [cell12374])
      exact ⟨E.1,E.2.trans (by norm_num [cell12374])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy47 (n := 12374) (by norm_num)
        (q := 1 - (cell12374 ⟨47,by decide⟩).lower)
        (by norm_num [cell12374]) (by norm_num [cell12374])
      exact ⟨E.1,E.2.trans (by norm_num [cell12374])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy48 (n := 12374) (by norm_num)
        (q := 1 - (cell12374 ⟨48,by decide⟩).lower)
        (by norm_num [cell12374]) (by norm_num [cell12374])
      exact ⟨E.1,E.2.trans (by norm_num [cell12374])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy49 (n := 12374) (by norm_num)
        (q := 1 - (cell12374 ⟨49,by decide⟩).lower)
        (by norm_num [cell12374]) (by norm_num [cell12374])
      exact ⟨E.1,E.2.trans (by norm_num [cell12374])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy50 (n := 12374) (by norm_num)
        (q := 1 - (cell12374 ⟨50,by decide⟩).lower)
        (by norm_num [cell12374]) (by norm_num [cell12374])
      exact ⟨E.1,E.2.trans (by norm_num [cell12374])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy51 (n := 12374) (by norm_num)
        (q := 1 - (cell12374 ⟨51,by decide⟩).lower)
        (by norm_num [cell12374]) (by norm_num [cell12374])
      exact ⟨E.1,E.2.trans (by norm_num [cell12374])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S0.uniformEnergy52 (n := 12374) (by norm_num)
        (q := 1 - (cell12374 ⟨52,by decide⟩).lower)
        (by norm_num [cell12374]) (by norm_num [cell12374])
      exact ⟨E.1,E.2.trans (by norm_num [cell12374])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12374

/-! Source-cell containment and simple scalar guards at 12374. -/
namespace BstLean.Part269.N12374
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12374)
open BstLean.Part268 (cell12374)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12374 ⟨10,by decide⟩).lower ∧ (cell12374 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12374 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12374 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12374 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12374 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12374 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12374,cell12374,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12374 ⟨11,by decide⟩).lower ∧ (cell12374 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12374 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12374 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12374 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12374 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12374 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12374,cell12374,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12374 ⟨12,by decide⟩).lower ∧ (cell12374 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12374 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12374 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12374 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12374 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12374 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12374,cell12374,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12374 ⟨13,by decide⟩).lower ∧ (cell12374 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12374 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12374 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12374 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12374 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12374 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12374,cell12374,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12374 ⟨14,by decide⟩).lower ∧ (cell12374 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12374 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12374 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12374 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12374 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12374 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12374,cell12374,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12374 ⟨15,by decide⟩).lower ∧ (cell12374 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12374 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12374 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12374 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12374 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12374 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12374,cell12374,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12374 ⟨16,by decide⟩).lower ∧ (cell12374 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12374 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12374 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12374 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12374 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12374 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12374,cell12374,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12374 ⟨17,by decide⟩).lower ∧ (cell12374 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12374 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12374 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12374 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12374 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12374 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12374,cell12374,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12374 ⟨18,by decide⟩).lower ∧ (cell12374 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12374 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12374 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12374 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12374 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12374 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12374,cell12374,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12374 ⟨19,by decide⟩).lower ∧ (cell12374 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12374 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12374 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12374 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12374 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12374 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12374,cell12374,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12374 ⟨20,by decide⟩).lower ∧ (cell12374 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12374 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12374 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12374 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12374 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12374 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12374,cell12374,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12374 ⟨21,by decide⟩).lower ∧ (cell12374 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12374 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12374 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12374 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12374 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12374 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12374,cell12374,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12374 ⟨22,by decide⟩).lower ∧ (cell12374 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12374 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12374 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12374 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12374 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12374 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12374,cell12374,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12374 ⟨23,by decide⟩).lower ∧ (cell12374 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12374 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12374 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12374 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12374 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12374 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12374,cell12374,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12374 ⟨24,by decide⟩).lower ∧ (cell12374 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12374 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12374 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12374 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12374 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12374 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12374,cell12374,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12374 ⟨25,by decide⟩).lower ∧ (cell12374 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12374 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12374 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12374 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12374 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12374 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12374,cell12374,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12374 ⟨26,by decide⟩).lower ∧ (cell12374 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12374 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12374 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12374 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12374 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12374 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12374,cell12374,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12374 ⟨27,by decide⟩).lower ∧ (cell12374 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12374 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12374 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12374 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12374 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12374 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12374,cell12374,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12374 ⟨28,by decide⟩).lower ∧ (cell12374 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12374 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12374 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12374 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12374 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12374 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12374,cell12374,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12374 ⟨29,by decide⟩).lower ∧ (cell12374 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12374 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12374 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12374 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12374 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12374 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12374,cell12374,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12374 ⟨30,by decide⟩).lower ∧ (cell12374 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12374 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12374 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12374 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12374 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12374 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12374,cell12374,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12374 ⟨31,by decide⟩).lower ∧ (cell12374 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12374 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12374 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12374 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12374 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12374 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12374,cell12374,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12374 ⟨32,by decide⟩).lower ∧ (cell12374 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12374 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12374 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12374 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12374 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12374 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12374,cell12374,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12374 ⟨33,by decide⟩).lower ∧ (cell12374 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12374 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12374 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12374 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12374 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12374 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12374,cell12374,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12374 ⟨34,by decide⟩).lower ∧ (cell12374 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12374 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12374 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12374 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12374 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12374 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12374,cell12374,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12374 ⟨35,by decide⟩).lower ∧ (cell12374 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12374 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12374 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12374 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12374 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12374 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12374,cell12374,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12374 ⟨36,by decide⟩).lower ∧ (cell12374 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12374 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12374 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12374 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12374 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12374 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12374,cell12374,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12374 ⟨37,by decide⟩).lower ∧ (cell12374 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12374 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12374 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12374 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12374 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12374 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12374,cell12374,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12374 ⟨38,by decide⟩).lower ∧ (cell12374 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12374 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12374 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12374 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12374 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12374 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12374,cell12374,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12374 ⟨39,by decide⟩).lower ∧ (cell12374 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12374 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12374 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12374 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12374 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12374 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12374,cell12374,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12374 ⟨40,by decide⟩).lower ∧ (cell12374 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12374 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12374 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12374 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12374 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12374 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12374,cell12374,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12374 ⟨41,by decide⟩).lower ∧ (cell12374 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12374 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12374 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12374 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12374 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12374 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12374,cell12374,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12374 ⟨42,by decide⟩).lower ∧ (cell12374 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12374 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12374 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12374 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12374 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12374 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12374,cell12374,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12374 ⟨43,by decide⟩).lower ∧ (cell12374 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12374 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12374 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12374 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12374 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12374 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12374,cell12374,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12374 ⟨44,by decide⟩).lower ∧ (cell12374 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12374 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12374 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12374 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12374 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12374 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12374,cell12374,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12374 ⟨45,by decide⟩).lower ∧ (cell12374 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12374 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12374 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12374 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12374 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12374 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12374,cell12374,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12374 ⟨46,by decide⟩).lower ∧ (cell12374 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12374 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12374 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12374 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12374 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12374 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12374,cell12374,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12374 ⟨47,by decide⟩).lower ∧ (cell12374 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12374 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12374 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12374 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12374 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12374 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12374,cell12374,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12374 ⟨48,by decide⟩).lower ∧ (cell12374 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12374 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12374 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12374 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12374 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12374 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12374,cell12374,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12374 ⟨49,by decide⟩).lower ∧ (cell12374 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12374 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12374 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12374 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12374 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12374 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12374,cell12374,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12374 ⟨50,by decide⟩).lower ∧ (cell12374 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12374 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12374 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12374 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12374 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12374 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12374,cell12374,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12374 ⟨51,by decide⟩).lower ∧ (cell12374 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12374 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12374 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12374 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12374 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12374 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12374,cell12374,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12374 ⟨52,by decide⟩).lower ∧ (cell12374 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12374 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12374 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12374 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12374 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12374 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12374,cell12374,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12374 i).lower ∧
    (cell12374 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12374 i).upper ≤ (0.532 : ℝ) ∧
    (cell12374 i).centre ≤ (0.1 : ℝ) ∧ (cell12374 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12374 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12374 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12374

/-! The local source numeric instances at 12374 have no network premises. -/
namespace BstLean.Part269.N12374
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12374)
open BstLean.Part268 (cell12374)

noncomputable def sourceNumerics12374 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12374 (cell12374 i)
      scalarRow12374.M scalarRow12374.H scalarRow12374.xi := by
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
    energy_allowance := scalarRow12374.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12374]
    centre_nonneg := (scalarRow12374.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D0.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12374])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12374